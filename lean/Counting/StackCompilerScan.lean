import Counting.StackCompiler

namespace Counting.StackMachine.Compiler
open Machine

def oneCounter (program : StackMachine.Program) : Fin (Registers program+1) :=
  ⟨1, by dsimp [Registers]; omega⟩

def atRegister {program : StackMachine.Program} (config : StackMachine.Config program)
    (register : Register program) : Configuration program :=
  ⟨scan config.control (oneCounter program), ⟨(before config.store register).reverse++[.mark],
    (block (config.store register)++after config.store register).headD .blank,
    (block (config.store register)++after config.store register).tail⟩⟩

theorem to_register {program : StackMachine.Program} (config : StackMachine.Config program)
    (register : Register program)
    (start : code program (entry config.control) .mark =
      some (scan config.control ⟨register.val+1, by have := register.isLt; dsimp [Registers]; omega⟩, .move .right)) :
    run (transition program) ((before config.store register).length+1) (atEntry config) =
      some (atRegister config register) := by
  have taken : ((stores config.store).take register.val).length = register.val := by
    rw [List.length_take, stores_length, Nat.min_eq_left (Nat.le_of_lt register.isLt)]
  have bounded : ((stores config.store).take register.val).length < Registers program := by
    rw [taken]
    exact register.isLt
  have scanned := FiniteControl.embed_run (code program) (StackScan.scanProgram (Registers program))
    (scan config.control) (fun counter symbol next action => scan_instruction program config.control counter next symbol action)
    _ (StackScan.scan_blocks_run (Registers program) ((stores config.store).take register.val)
      bounded [.mark] (block (config.store register)++after config.store register))
  have first : transition program (atEntry config) =
      some ⟨scan config.control ⟨register.val+1, by have := register.isLt; dsimp [Registers]; omega⟩,
        ⟨[.mark], (before config.store register++block (config.store register)++after config.store register).headD .blank,
          (before config.store register++block (config.store register)++after config.store register).tail⟩⟩ := by
    simp only [atEntry, encoded_split config register, Tape.ofWord, List.headD_cons, List.tail_cons,
      transition, FiniteControl.step, start, Option.map_some, Tape.move]
  rw [run, first, Option.bind_some]
  simpa only [StackScan.scanAt, taken, before, List.append_assoc, atRegister, oneCounter] using scanned

theorem return_finish (program : StackMachine.Program) (control : StackMachine.Control program)
    (left : List Symbol) (head : Symbol) (right : List Symbol)
    (symbols : ∀ symbol ∈ left, symbol ≠ .mark) (current : head ≠ .mark) :
    run (transition program) (left.length+2)
      ⟨returning control, ⟨left++[.mark],head,right⟩⟩ =
      some ⟨entry control, ⟨[],.mark,left.reverse++head::right⟩⟩ := by
  have returned := FiniteControl.embed_run (code program) StackScan.returnProgram
    (fun _ => returning control) (fun phase symbol next action => return_instruction program control phase next symbol action)
    _ (StackScan.return_run left head right symbols current)
  dsimp only [StackScan.returnAt] at returned
  have last : transition program ⟨returning control, ⟨[],.mark,left.reverse++head::right⟩⟩ =
      some ⟨entry control, ⟨[],.mark,left.reverse++head::right⟩⟩ := rfl
  rw [show left.length+2 = (left.length+1)+1 by omega, run_add]
  change (run (transition program) (left.length+1) _).bind _ = _
  rw [returned, Option.bind_some]
  exact last

theorem return_content_finish (program : StackMachine.Program) (control : StackMachine.Control program)
    (content : List Symbol) (symbols : ∀ symbol ∈ content, symbol ≠ .mark) :
    run (transition program) (content.length+2)
      ⟨returning control, ⟨content.reverse++[.mark],.blank,[]⟩⟩ =
      some ⟨entry control, ⟨[],.mark,content++[.blank]⟩⟩ := by
  simpa only [List.length_reverse, List.reverse_reverse] using
    return_finish program control content.reverse .blank []
      (by simpa only [List.mem_reverse] using symbols) (by decide)

end Counting.StackMachine.Compiler
