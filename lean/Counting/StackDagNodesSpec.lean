import Counting.StackDagNodesLoop

namespace Counting.StackMachine.DagValidation

theorem nodeRangeCheck_iff (values : List Executable.Node) (start count : Nat) :
    nodeRangeCheck values start count=true ↔
      ∀ i,start≤ i → i<start+count → nodeCondition values i (values[i]?.getD default)=true := by
  induction count generalizing start with
  | zero=>
    simp only [nodeRangeCheck,Nat.add_zero,true_iff]
    intro i lower upper
    omega
  | succ count ih=>
    rw [nodeRangeCheck,Bool.and_eq_true,ih]
    constructor
    · rintro ⟨first,rest⟩ i lower upper
      by_cases equal : i=start
      · simpa only [equal] using first
      · exact rest i (by omega) (by omega)
    · intro all
      exact ⟨all start le_rfl (by omega),fun i lower upper=>all i (by omega) (by omega)⟩

theorem nodeRangeCheck_vista (vista : Executable.Vista) :
    nodeRangeCheck vista.nodes.toList 0 vista.nodes.size=(List.range vista.nodes.size).all (Executable.nodeValid vista):=by
  apply Bool.eq_iff_iff.mpr
  rw [nodeRangeCheck_iff,List.all_eq_true]
  simp only [List.mem_range,Nat.zero_add,Nat.zero_le,forall_true_left]
  apply forall_congr'
  intro i
  apply imp_congr_right
  intro _
  have same : vista.nodes.toList[i]?.getD default=vista.node i:=by simp [Executable.Vista.node]
  rw [same,nodeCondition_vista]

end Counting.StackMachine.DagValidation
