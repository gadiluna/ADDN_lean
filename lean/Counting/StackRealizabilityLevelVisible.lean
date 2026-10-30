import Counting.StackRealizabilityLevelSpec

namespace Counting.StackMachine.RealizabilityCheck

theorem levelRangeSum_vista (vista : Executable.Vista) (weights : Array Nat) (r : Nat)
    (length : weights.size=vista.nodes.size) :
    levelRangeSum vista.nodes.toList r 0 weights.toList=
      ((Executable.levelNodes vista r).map (RealizabilityVerifier.weight weights)).sum:=by
  rw [levelRangeSum_eq_map_range,Executable.levelNodes,RealizabilityVerifier.filtered_sum_scan]
  simp only [Array.length_toList,length,Nat.zero_add,beq_iff_eq]
  apply congrArg List.sum
  apply List.map_congr_left
  intro index member
  have nodeInside : index<vista.nodes.size:=List.mem_range.mp member
  have weightInside : index<weights.size:=by omega
  have nodeList : index<vista.nodes.toList.length:=by simpa only [Array.length_toList] using nodeInside
  have weightList : index<weights.toList.length:=by simpa only [Array.length_toList] using weightInside
  simp only [levelContribution,List.getElem?_eq_getElem nodeList,List.getElem?_eq_getElem weightList,
    Option.getD_some,Array.getElem_toList,Executable.Vista.node,Array.getElem?_eq_getElem nodeInside,
    RealizabilityVerifier.weight,Array.getElem?_eq_getElem weightInside]

end Counting.StackMachine.RealizabilityCheck
