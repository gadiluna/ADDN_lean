import Counting.MachineStackScan
import Counting.MachineArithmeticClean

namespace Counting.Machine.StackBootstrap

/-- Prepare a marker and a fixed number of stack delimiters. Every shift,
write and return movement is a primitive machine transition. -/
def program (registers : Nat) : Program where
  states := 2*registers+4
  code state symbol :=
    if state.val = 0 then some (⟨1, by omega⟩, .move .left)
    else if state.val = 1 then some (⟨2, by omega⟩, .write .mark)
    else if state.val = 2 then some (⟨3, by omega⟩, .move .right)
    else if state.val = 3 then
      if symbol = .blank then some (⟨4, by omega⟩, .write .blank)
      else some (state, .move .right)
    else if inside : state.val < 2*registers+4 then
      some (⟨state.val+1, by omega⟩,
        if state.val % 2 = 0 then .write .separator else .move .right)
    else if symbol = .mark then none else some (state, .move .left)
  accept state := state.val == 2*registers+4

def bootAt (registers : Nat) (control : Control (program registers)) (left : List Symbol)
    (head : Symbol) (right : List Symbol) : Config (program registers) := ⟨control, ⟨left,head,right⟩⟩

def phase (registers count : Nat) (bound : count ≤ registers) : Control (program registers) :=
  ⟨4+2*count, by dsimp [program]; omega⟩

def finish (registers : Nat) : Control (program registers) := phase registers registers le_rfl

theorem setup_run (registers : Nat) (input : List Bool) :
    run (step (program registers)) 3 (initial (program registers) input) =
      some (bootAt registers ⟨3, by dsimp [program]; omega⟩ [.mark]
        ((input.map bitSymbol).headD .blank) (input.map bitSymbol).tail) := by
  rfl

theorem scan_run (registers : Nat) (input : List Bool) (left : List Symbol) :
    run (step (program registers)) (input.length+1)
      (bootAt registers ⟨3, by dsimp [program]; omega⟩ left
        ((input.map bitSymbol).headD .blank) (input.map bitSymbol).tail) =
      some (bootAt registers (phase registers 0 (Nat.zero_le _))
        (input.reverse.map bitSymbol++left) .blank []) := by
  induction input generalizing left with
  | nil => rfl
  | cons bit input ih =>
      have first : step (program registers)
          (bootAt registers ⟨3, by dsimp [program]; omega⟩ left
            (((bit::input).map bitSymbol).headD .blank) ((bit::input).map bitSymbol).tail) =
          some (bootAt registers ⟨3, by dsimp [program]; omega⟩ (bitSymbol bit::left)
            ((input.map bitSymbol).headD .blank) (input.map bitSymbol).tail) := by cases bit <;> rfl
      rw [List.length_cons, Nat.add_right_comm _ 1 1, run, first, Option.bind_some, ih]
      simp only [bootAt, List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
        List.append_assoc, List.singleton_append]

theorem append_two (registers count : Nat) (within : count < registers) (left : List Symbol) :
    run (step (program registers)) 2
      (bootAt registers (phase registers count within.le) left .blank []) =
      some (bootAt registers (phase registers (count+1) (by omega)) (.separator::left) .blank []) := by
  have first : 4+2*count < 2*registers+4 := by omega
  have second : 4+2*count+1 < 2*registers+4 := by omega
  simp only [run, step, program, bootAt, phase]
  simp only [show ¬(4+2*count = 0) by omega, show ¬(4+2*count = 1) by omega,
    show ¬(4+2*count = 2) by omega, show ¬(4+2*count = 3) by omega, first, if_false, if_true, dif_pos,
    show (4+2*count)%2=0 by omega, Option.map_some, Option.bind_some, Tape.write]
  simp only [show ¬(4+2*count+1=0) by omega, show ¬(4+2*count+1=1) by omega,
    show ¬(4+2*count+1=2) by omega, show ¬(4+2*count+1=3) by omega, second, if_false, dif_pos,
    show ¬((4+2*count+1)%2=0) by omega, Option.map_some, Option.bind_some, Tape.move]
  congr 3

theorem append_run (registers count remaining : Nat) (total : count+remaining=registers)
    (left : List Symbol) :
    run (step (program registers)) (2*remaining)
      (bootAt registers (phase registers count (by omega)) left .blank []) =
      some (bootAt registers (finish registers) (List.replicate remaining .separator++left) .blank []) := by
  induction remaining generalizing count left with
  | zero =>
      have equal : count=registers := by omega
      subst count
      rfl
  | succ remaining ih =>
      rw [show 2*(remaining+1)=2+2*remaining by omega, run_add,
        append_two registers count (by omega) left, Option.bind_some,
        ih (count+1) (by omega) (.separator::left)]
      simp only [List.replicate_succ', List.append_assoc, List.singleton_append]

def embedReturn (registers : Nat) (config : Config StackScan.returnProgram) : Config (program registers) :=
  ⟨finish registers, config.tape⟩

theorem return_simulates (registers : Nat) (config : Config StackScan.returnProgram) :
    (step StackScan.returnProgram config).map (embedReturn registers) =
      step (program registers) (embedReturn registers config) := by
  have q0 : ¬(4+2*registers=0) := by omega
  have q1 : ¬(4+2*registers=1) := by omega
  have q2 : ¬(4+2*registers=2) := by omega
  have q3 : ¬(4+2*registers=3) := by omega
  have last : ¬(4+2*registers<2*registers+4) := by omega
  simp only [step, StackScan.returnProgram, embedReturn, finish, phase, program,
    q0, q1, q2, q3, last, if_false, dite_false]
  by_cases mark : config.tape.head = .mark
  · simp only [mark, if_true, Option.map_none]
  · simp only [mark, if_false, Option.map_some, embedReturn, finish, phase]
    rfl

theorem rewind_run (registers : Nat) (content : List Symbol)
    (symbols : ∀ symbol ∈ content, symbol ≠ .mark) :
    run (step (program registers)) (content.length+1)
      (bootAt registers (finish registers) (content.reverse++[.mark]) .blank []) =
      some (bootAt registers (finish registers) [] .mark (content++[.blank])) := by
  have sim := run_simulation (step StackScan.returnProgram) (step (program registers))
    (embedReturn registers) (return_simulates registers) (content.length+1)
      (StackScan.returnAt (content.reverse++[.mark]) .blank [])
  rw [StackScan.return_content content symbols, Option.map_some] at sim
  exact sim.symm

def output (registers : Nat) (input : List Bool) : Config (program registers) :=
  bootAt registers (finish registers) [] .mark
    ((input.map bitSymbol ++ List.replicate registers .separator)++[.blank])

/-- Bootstrap the actual binary machine input into the complete stack tape,
including every delimiter and a measured return to the marker. -/
theorem bootstrap_run (registers : Nat) (input : List Bool) :
    run (step (program registers)) (2*input.length+3*registers+5)
      (initial (program registers) input) = some (output registers input) := by
  have time : 2*input.length+3*registers+5 =
      3 + ((input.length+1)+(2*registers+(input.length+registers+1))) := by omega
  rw [time, run_add, setup_run, Option.bind_some, run_add, scan_run, Option.bind_some,
    run_add, append_run registers 0 registers (Nat.zero_add registers), Option.bind_some]
  let content := input.map bitSymbol ++ List.replicate registers .separator
  have represented : List.replicate registers .separator ++ (input.reverse.map bitSymbol ++ [.mark]) =
      content.reverse ++ [.mark] := by simp [content, List.reverse_append, List.reverse_replicate, List.map_reverse, List.append_assoc]
  rw [represented]
  have length : content.length = input.length+registers := by simp [content]
  rw [← length, rewind_run]
  · rfl
  · intro symbol member
    simp only [content, List.mem_append, List.mem_map, List.mem_replicate] at member
    rcases member with ⟨bit,_,rfl⟩ | ⟨_,rfl⟩
    · cases bit <;> decide
    · decide

theorem bootstrap_halted (registers : Nat) (input : List Bool) :
    step (program registers) (output registers input) = none := by
  have sim := return_simulates registers
    (StackScan.returnAt [] .mark ((input.map bitSymbol ++ List.replicate registers .separator)++[.blank]))
  rw [StackScan.return_halted, Option.map_none] at sim
  exact sim.symm

theorem trailing_blank (word : List Symbol) :
    Turing.ListBlank.mk (word++[Symbol.blank]) = Turing.ListBlank.mk word := by
  rw [← Turing.ListBlank.append_mk]
  have blank : Turing.ListBlank.mk [Symbol.blank] = Turing.ListBlank.mk ([] : List Symbol) := blank_list_denotes 1
  change Turing.ListBlank.append word (Turing.ListBlank.mk [.blank]) = _
  rw [blank, Turing.ListBlank.append_mk, List.append_nil]

theorem bootstrap_tape (registers : Nat) (input : List Bool) :
    (output registers input).tape.denotes =
      Turing.Tape.mk₁ (.mark :: (input.map bitSymbol ++ List.replicate registers .separator)) := by
  change (⟨.mark, Turing.ListBlank.mk [],
    Turing.ListBlank.mk ((input.map bitSymbol ++ List.replicate registers .separator)++[.blank])⟩ : Turing.Tape Symbol) =
    ⟨.mark, Turing.ListBlank.mk [], Turing.ListBlank.mk (input.map bitSymbol ++ List.replicate registers .separator)⟩
  rw [trailing_blank]

end Counting.Machine.StackBootstrap
