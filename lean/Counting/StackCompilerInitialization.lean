import Counting.StackCompilerSimulation

namespace Counting.StackMachine.Compiler
open Machine

theorem encode_entry_zero (program : StackMachine.Program) : encode program (entry 0) = 0 := by
  apply Fin.ext
  rfl

theorem initial_encoded (program : StackMachine.Program) (input : List Bool) :
    (StackMachine.initial program input).encoded =
      .mark :: (input.map bitSymbol ++ List.replicate (Registers program) .separator) := by
  unfold StackMachine.Config.encoded StackMachine.initial
  rw [List.finRange_succ]
  simp only [List.flatMap_cons, List.flatMap_map, Fin.succ_ne_zero, if_false, block,
    List.map_nil, List.nil_append, ite_true]
  have flat (values : List (Fin (program.extraRegisters+1))) :
      values.flatMap (fun _ => [Symbol.separator]) = List.replicate values.length Symbol.separator := by
    induction values with
    | nil => rfl
    | cons value values ih => simp only [List.flatMap_cons, ih, List.singleton_append,
        List.length_cons, List.replicate_succ]
  rw [flat]
  simp [Registers, List.append_assoc, List.replicate_succ]

theorem physical_initial (program : StackMachine.Program) (input : List Bool) :
    physical (StackMachine.initial program input) =
      (⟨0, Tape.ofWord (.mark :: (input.map bitSymbol ++ List.replicate (Registers program) .separator))⟩ :
        Machine.Config (machine program)) := by
  change (⟨encode program (entry 0), Tape.ofWord (StackMachine.initial program input).encoded⟩ :
    Machine.Config (machine program)) = _
  rw [encode_entry_zero, initial_encoded]
  rfl

end Counting.StackMachine.Compiler
