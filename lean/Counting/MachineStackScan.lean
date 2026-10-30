import Counting.StackMachine

namespace Counting.Machine.StackScan

/-- The counter is finite control. State 1 is the destination; a separator
consumes one block and all other cells consume only one tape movement. -/
def scanProgram (registers : Nat) : Program where
  states := registers
  code state symbol :=
    if state.val ≤ 1 then none else
      some ((if symbol = .separator then
        ⟨state.val-1, by have := state.isLt; omega⟩ else state), .move .right)
  accept state := state == 1

def scanAt (registers : Nat) (state : Fin (registers+1)) (left data : List Symbol) :
    Config (scanProgram registers) := ⟨state, ⟨left, data.headD .blank, data.tail⟩⟩

theorem scan_plain (registers : Nat) (state : Fin (registers+1)) (active : 1 < state.val)
    (left plain suffix : List Symbol) (symbols : ∀ symbol ∈ plain, symbol ≠ .separator) :
    run (step (scanProgram registers)) plain.length (scanAt registers state left (plain++suffix)) =
      some (scanAt registers state (plain.reverse++left) suffix) := by
  induction plain generalizing left with
  | nil => rfl
  | cons symbol plain ih =>
      have notSeparator := symbols symbol List.mem_cons_self
      have after : step (scanProgram registers) (scanAt registers state left ((symbol::plain)++suffix)) =
          some (scanAt registers state (symbol::left) (plain++suffix)) := by
        simp only [step, scanProgram, Nat.not_le.mpr active, if_false, notSeparator, Option.map_some,
          scanAt, List.cons_append, List.headD_cons, List.tail_cons, Tape.move]
      rw [List.length_cons, run, after, Option.bind_some,
        ih (symbol::left) (fun value member => symbols value (List.mem_cons_of_mem symbol member))]
      simp only [scanAt, List.reverse_cons, List.append_assoc, List.singleton_append]

/-- Scan precisely the selected number of encoded stack blocks. -/
theorem scan_blocks_run (registers : Nat) (blocks : List (List Bool))
    (bounded : blocks.length < registers) (left suffix : List Symbol) :
    run (step (scanProgram registers)) (blocks.flatMap StackMachine.block).length
      (scanAt registers ⟨blocks.length+1, by omega⟩ left (blocks.flatMap StackMachine.block ++ suffix)) =
      some (scanAt registers ⟨1, by omega⟩ ((blocks.flatMap StackMachine.block).reverse++left) suffix) := by
  induction blocks generalizing left with
  | nil => rfl
  | cons bits blocks ih =>
      let state : Fin (registers+1) := ⟨(bits::blocks).length+1, by omega⟩
      have active : 1 < state.val := by dsimp [state]; omega
      have noSeparators : ∀ symbol ∈ bits.map bitSymbol, symbol ≠ .separator := by
        intro symbol member
        obtain ⟨bit, _, rfl⟩ := List.mem_map.mp member
        cases bit <;> decide
      have first := scan_plain registers state active left (bits.map bitSymbol)
        (.separator :: (blocks.flatMap StackMachine.block ++ suffix)) noSeparators
      have crossing : step (scanProgram registers)
          (scanAt registers state ((bits.map bitSymbol).reverse++left)
            (.separator :: (blocks.flatMap StackMachine.block ++ suffix))) =
          some (scanAt registers ⟨blocks.length+1, by simp only [List.length_cons] at bounded; omega⟩
            (.separator :: ((bits.map bitSymbol).reverse++left))
            (blocks.flatMap StackMachine.block ++ suffix)) := by
        simp only [step, scanProgram, scanAt, state, List.length_cons, Nat.add_sub_cancel,
          List.headD_cons, List.tail_cons, Tape.move]
        rfl
      have time : ((bits::blocks).flatMap StackMachine.block).length =
          (bits.map bitSymbol).length + (1+(blocks.flatMap StackMachine.block).length) := by
        simp [StackMachine.block]
        omega
      rw [time, run_add]
      simp only [List.flatMap_cons, StackMachine.block, List.append_assoc, List.singleton_append]
      change (run (step (scanProgram registers)) (bits.map bitSymbol).length
        (scanAt registers state left ((bits.map bitSymbol)++
          (.separator :: (blocks.flatMap StackMachine.block ++ suffix))))).bind _ = _
      rw [first, Option.bind_some, Nat.one_add, run, crossing, Option.bind_some,
        ih (by simp only [List.length_cons] at bounded; omega)
          (.separator :: ((bits.map bitSymbol).reverse++left))]
      simp [scanAt, List.reverse_append, List.append_assoc]

theorem scan_halted (registers : Nat) (positive : 0 < registers) (left data : List Symbol) :
    step (scanProgram registers) (scanAt registers ⟨1, by omega⟩ left data) = none := rfl

def returnProgram : Program where
  states := 0
  code _ symbol := if symbol = .mark then none else some (0, .move .left)
  accept _ := true

def returnAt (left : List Symbol) (head : Symbol) (right : List Symbol) : Config returnProgram :=
  ⟨0, ⟨left,head,right⟩⟩

theorem return_run (left : List Symbol) (head : Symbol) (right : List Symbol)
    (symbols : ∀ symbol ∈ left, symbol ≠ .mark) (current : head ≠ .mark) :
    run (step returnProgram) (left.length+1) (returnAt (left++[.mark]) head right) =
      some (returnAt [] .mark (left.reverse++head::right)) := by
  induction left generalizing head right with
  | nil =>
      simp only [List.length_nil, List.nil_append, run, step, returnProgram,
        returnAt, current, if_false, Option.map_some, Tape.move, List.tail_cons, List.headD_cons,
        Option.bind_some]
      rfl
  | cons symbol left ih =>
      have notMark := symbols symbol List.mem_cons_self
      have next : step returnProgram (returnAt ((symbol::left)++[.mark]) head right) =
          some (returnAt (left++[.mark]) symbol (head::right)) := by
        simp only [step, returnProgram, returnAt, current, if_false, Option.map_some, Tape.move,
          List.cons_append, List.tail_cons, List.headD_cons]
        rfl
      rw [List.length_cons, Nat.add_right_comm _ 1 1, run, next, Option.bind_some,
        ih symbol (head::right) (fun value member => symbols value (List.mem_cons_of_mem symbol member)) notMark]
      simp only [returnAt, List.reverse_cons, List.append_assoc, List.singleton_append]

/-- The return trip after insertion/deletion is measured explicitly. -/
theorem return_content (content : List Symbol)
    (symbols : ∀ symbol ∈ content, symbol ≠ .mark) :
    run (step returnProgram) (content.length+1) (returnAt (content.reverse++[.mark]) .blank []) =
      some (returnAt [] .mark (content++[.blank])) := by
  simpa only [List.length_reverse, List.reverse_reverse] using
    return_run content.reverse .blank [] (by simpa only [List.mem_reverse] using symbols) (by decide)

theorem return_halted (right : List Symbol) : step returnProgram (returnAt [] .mark right) = none := rfl

end Counting.Machine.StackScan
