import Counting.MachineStackBootstrap

namespace Counting.Machine.StackCleanup

/-- Keep the second stack and erase every work cell. All actions are primitive
writes or unit moves; there is no bulk erase or tape translation operation. -/
def program : Program where
  states := 10
  code state symbol := match state.val with
    | 0 => some (1, .write .blank)
    | 1 => some (2, .move .right)
    | 2 => if symbol = .separator then some (4, .write .mark) else some (3, .write .blank)
    | 3 => some (2, .move .right)
    | 4 => some (5, .move .right)
    | 5 => if symbol = .separator then some (6, .write .blank) else some (5, .move .right)
    | 6 => some (7, .move .right)
    | 7 => if symbol = .blank then some (8, .move .left) else some (6, .write .blank)
    | 8 => if symbol = .mark then some (9, .write .blank) else some (8, .move .left)
    | 9 => some (10, .move .right)
    | _ => none
  accept state := state == 10

def cleanAt (control : Control program) (left : List Symbol) (head : Symbol)
    (right : List Symbol) : Config program := ⟨control, ⟨left,head,right⟩⟩

def cleanData (control : Control program) (left data : List Symbol) : Config program :=
  cleanAt control left (data.headD .blank) data.tail

theorem erase_first (first : List Bool) (left rest : List Symbol) :
    run (step program) (2*first.length+2)
      (cleanData 2 left (first.map bitSymbol ++ .separator::rest)) =
      some (cleanData 5 (.mark :: (List.replicate first.length .blank++left)) rest) := by
  induction first generalizing left with
  | nil => rfl
  | cons bit first ih =>
      have two : run (step program) 2
          (cleanData 2 left ((bit::first).map bitSymbol ++ .separator::rest)) =
          some (cleanData 2 (.blank::left) (first.map bitSymbol ++ .separator::rest)) := by
        cases bit <;> rfl
      rw [List.length_cons, show 2*(first.length+1)+2 = 2+(2*first.length+2) by omega,
        run_add, two, Option.bind_some, ih]
      simp only [List.replicate_succ', List.append_assoc, List.singleton_append]

theorem scan_output (output : List Bool) (left rest : List Symbol) :
    run (step program) output.length
      (cleanData 5 left (output.map bitSymbol ++ .separator::rest)) =
      some (cleanAt 5 ((output.map bitSymbol).reverse++left) .separator rest) := by
  induction output generalizing left with
  | nil => rfl
  | cons bit output ih =>
      have first : step program (cleanData 5 left ((bit::output).map bitSymbol ++ .separator::rest)) =
          some (cleanData 5 (bitSymbol bit::left) (output.map bitSymbol ++ .separator::rest)) := by
        cases bit <;> rfl
      rw [List.length_cons, run, first, Option.bind_some, ih]
      simp only [List.map_cons, List.reverse_cons, List.append_assoc, List.singleton_append]

theorem erase_suffix (data left : List Symbol)
    (nonblank : ∀ symbol ∈ data, symbol ≠ .blank) :
    run (step program) (2*data.length) (cleanData 7 left data) =
      some (cleanAt 7 (List.replicate data.length .blank++left) .blank []) := by
  induction data generalizing left with
  | nil => rfl
  | cons symbol data ih =>
      have notBlank := nonblank symbol List.mem_cons_self
      have two : run (step program) 2 (cleanData 7 left (symbol::data)) =
          some (cleanData 7 (.blank::left) data) := by
        simp only [run, step, program, cleanData, cleanAt, List.headD_cons, List.tail_cons,
          notBlank, if_false, Tape.write, Tape.move]
        rfl
      rw [List.length_cons, show 2*(data.length+1)=2+2*data.length by omega,
        run_add, two, Option.bind_some,
        ih (.blank::left) (fun value member => nonblank value (List.mem_cons_of_mem symbol member))]
      simp only [List.replicate_succ', List.append_assoc, List.singleton_append]

theorem rewind (left erased : List Symbol) (head : Symbol) (right : List Symbol)
    (symbols : ∀ symbol ∈ left, symbol ≠ .mark) (current : head ≠ .mark) :
    run (step program) (left.length+1) (cleanAt 8 (left++(.mark::erased)) head right) =
      some (cleanAt 8 erased .mark (left.reverse++head::right)) := by
  induction left generalizing head right with
  | nil =>
      simp only [List.length_nil, List.nil_append, run, step, program, cleanAt, current,
        if_false, Tape.move, List.tail_cons, List.headD_cons]
      rfl
  | cons symbol left ih =>
      have notMark := symbols symbol List.mem_cons_self
      have next : step program (cleanAt 8 ((symbol::left)++(.mark::erased)) head right) =
          some (cleanAt 8 (left++(.mark::erased)) symbol (head::right)) := by
        simp only [step, program, cleanAt, current, if_false, Tape.move,
          List.cons_append, List.tail_cons, List.headD_cons]
        rfl
      rw [List.length_cons, Nat.add_right_comm _ 1 1, run, next, Option.bind_some,
        ih symbol (head::right) (fun value member => symbols value (List.mem_cons_of_mem symbol member)) notMark]
      simp only [List.reverse_cons, List.append_assoc, List.singleton_append]

/-- Return over the erased suffix and retained output, stopping at the sole
marker. The first move out of the end blank is included. -/
theorem rewind_output (output : List Bool) (suffixLength : Nat) (erased : List Symbol) :
    run (step program) (suffixLength+output.length+2)
      (cleanAt 7 (List.replicate (suffixLength+1) .blank ++
        ((output.map bitSymbol).reverse ++ (.mark::erased))) .blank []) =
      some (cleanAt 8 erased .mark
        (output.map bitSymbol ++ List.replicate (suffixLength+2) .blank)) := by
  have first : step program
      (cleanAt 7 (List.replicate (suffixLength+1) .blank ++
        ((output.map bitSymbol).reverse ++ (.mark::erased))) .blank []) =
      some (cleanAt 8 (List.replicate suffixLength .blank ++
        ((output.map bitSymbol).reverse ++ (.mark::erased))) .blank [.blank]) := by
    simp only [List.replicate_succ, List.cons_append, step, program, cleanAt,
      if_true, Tape.move, List.tail_cons, List.headD_cons]
    rfl
  let before : List Symbol := List.replicate suffixLength .blank ++ (output.map bitSymbol).reverse
  have time : suffixLength+output.length+2 = (before.length+1)+1 := by simp [before]
  rw [time, run, first, Option.bind_some]
  rw [← List.append_assoc]
  change run (step program) (before.length+1)
    (cleanAt 8 (before++(.mark::erased)) .blank [.blank]) = _
  rw [rewind before erased .blank [.blank]]
  · simp only [before, List.reverse_append, List.reverse_reverse, List.reverse_replicate,
      List.append_assoc]
    rw [show List.replicate suffixLength Symbol.blank ++ [.blank,.blank] =
        List.replicate (suffixLength+2) .blank by rw [List.replicate_add]; rfl]
  · intro symbol member
    simp only [before, List.mem_append, List.mem_replicate, List.mem_reverse, List.mem_map] at member
    rcases member with ⟨_,rfl⟩ | ⟨bit,_,rfl⟩
    · decide
    · cases bit <;> decide
  · decide

def input (first output : List Bool) (tail : List Symbol) : Config program :=
  cleanAt 0 [] .mark
    (first.map bitSymbol ++ (.separator :: (output.map bitSymbol ++ (.separator::tail))))

def result (first output : List Bool) (tail : List Symbol) : Config program :=
  cleanData 10 (List.replicate (first.length+2) .blank)
    (output.map bitSymbol ++ List.replicate (tail.length+2) .blank)

theorem cleanup_run (first output : List Bool) (tail : List Symbol)
    (nonblank : ∀ symbol ∈ tail, symbol ≠ .blank) :
    run (step program) (2*first.length+2*output.length+3*tail.length+10)
      (input first output tail) = some (result first output tail) := by
  have setup : run (step program) 2 (input first output tail) =
      some (cleanData 2 [.blank]
        (first.map bitSymbol ++ .separator :: (output.map bitSymbol ++ .separator::tail))) := rfl
  have crossing : ∀ left, run (step program) 2 (cleanAt 5 left .separator tail) =
      some (cleanData 7 (.blank::left) tail) := fun _ => rfl
  have time : 2*first.length+2*output.length+3*tail.length+10 =
      2+((2*first.length+2)+(output.length+(2+(2*tail.length+((tail.length+output.length+2)+2))))) := by omega
  rw [time, run_add, setup, Option.bind_some, run_add, erase_first, Option.bind_some,
    run_add, scan_output, Option.bind_some, run_add, crossing, Option.bind_some,
    run_add, erase_suffix _ _ nonblank, Option.bind_some]
  have regroup : List.replicate tail.length Symbol.blank ++
      (.blank :: ((output.map bitSymbol).reverse ++
        (.mark :: (List.replicate first.length .blank ++ [.blank])))) =
      List.replicate (tail.length+1) .blank ++ ((output.map bitSymbol).reverse ++
        (.mark :: (List.replicate first.length .blank ++ [.blank]))) := by
    rw [List.replicate_succ', List.append_assoc, List.singleton_append]
  rw [regroup, run_add, rewind_output, Option.bind_some]
  have finish : ∀ erased data, run (step program) 2 (cleanAt 8 erased .mark data) =
      some (cleanData 10 (.blank::erased) data) := fun _ _ => rfl
  rw [finish]
  have erased : Symbol.blank :: (List.replicate first.length .blank ++ [.blank]) =
      List.replicate (first.length+2) .blank := by
    rw [← List.replicate_succ', ← List.replicate_succ]
  rw [erased]
  rfl

theorem cleanup_halted (first output : List Bool) (tail : List Symbol) :
    step program (result first output tail) = none := rfl

theorem trailing_blanks (word : List Symbol) (count : Nat) :
    Turing.ListBlank.mk (word++List.replicate count Symbol.blank) = Turing.ListBlank.mk word := by
  rw [← Turing.ListBlank.append_mk, blank_list_denotes, Turing.ListBlank.append_mk, List.append_nil]

theorem cleanData_denotes (control : Control program) (left data : List Symbol) :
    (cleanData control left data).tape.denotes = Turing.Tape.mk₂ left data := by
  cases data <;> rfl

/-- Every work cell has been erased, including all cells left of the output. -/
theorem cleanup_tape (first output : List Bool) (tail : List Symbol) :
    (result first output tail).tape.denotes = Turing.Tape.mk₁ (output.map bitSymbol) := by
  rw [result, cleanData_denotes]
  unfold Turing.Tape.mk₂ Turing.Tape.mk₁
  rw [blank_list_denotes, trailing_blanks]
  rfl

theorem cleanup_steps_le (first output : List Bool) (tail : List Symbol) :
    2*first.length+2*output.length+3*tail.length+10 ≤
      3*(.mark :: (first.map bitSymbol ++ (.separator ::
        (output.map bitSymbol ++ (.separator::tail))))).length+1 := by
  simp only [List.length_cons, List.length_append, List.length_map]
  omega

theorem input_tape (first output : List Bool) (tail : List Symbol) :
    (input first output tail).tape.denotes =
      Turing.Tape.mk₁ (.mark :: (first.map bitSymbol ++ (.separator ::
        (output.map bitSymbol ++ (.separator::tail))))) := rfl

end Counting.Machine.StackCleanup
