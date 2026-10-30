import Counting.StackDagKeyEncode

namespace Counting.StackMachine.DagUpdate.Key

theorem keyBudget_linear (node : Executable.Node) :
    keyBudget node ≤ 50*((Encoding.node.encode node).length+1) := by
  have leaderBound : (Encoding.natural.encode (if node.leader then 1 else 0)).length ≤ 3 := by
    cases node.leader <;> decide
  simp only [keyBudget,Encoding.bits_length,Encoding.sequence_length,Encoding.product,
    List.length_append,Encoding.natural_length,Encoding.node_length,Encoding.nodeBits,
    NodeMap.parentNumber]
  simp only [Encoding.natural_length] at leaderBound
  omega

theorem encodeKey_executes_linear (store : Routine.Store 62) (node : Executable.Node)
    (source : store 0=Encoding.node.encode node)
    (empty : ∀ r : Fin 64,r=3 ∨ (40 ≤ r.val ∧ r.val ≤ 44) ∨ r=49 → store r=[]) :
    ∃ time ≤ 50*((store 0).length+1),
      Routine.Executes encodeKey store time
        (Function.update (Function.update store 0 []) 3 (Encoding.sequence Encoding.natural node.key)) := by
  exact ⟨keyBudget node,by rw [source];exact keyBudget_linear node,encodeKey_executes store node source empty⟩

end Counting.StackMachine.DagUpdate.Key
