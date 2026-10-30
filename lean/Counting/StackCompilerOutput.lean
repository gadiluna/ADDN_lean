import Counting.StackCompilerInitialization

namespace Counting.StackMachine.Compiler
open Machine

theorem before_output {program : StackMachine.Program} (config : StackMachine.Config program) :
    before config.store 1 = block (config.store 0) := by
  have position : (1 : Register program).val = 1 := by
    rw [Fin.val_one]
  simp only [before, position, stores, List.finRange_succ, List.map_cons, List.take_succ_cons,
    List.take_zero, List.flatMap_cons, List.flatMap_nil, List.append_nil]

theorem encoded_output {program : StackMachine.Program} (config : StackMachine.Config program) :
    config.encoded = .mark :: ((config.store 0).map bitSymbol ++ .separator ::
      ((config.store 1).map bitSymbol ++ .separator :: after config.store 1)) := by
  rw [encoded_split config 1, before_output]
  simp [block, List.append_assoc]

theorem output_split_length {program : StackMachine.Program} (config : StackMachine.Config program) :
    (config.store 0).length+(config.store 1).length+(after config.store 1).length+3 = config.encoded.length := by
  rw [encoded_output]
  simp only [List.length_cons, List.length_append, List.length_map]
  omega

end Counting.StackMachine.Compiler
