import Counting.StackRealizabilityLevelItem
import Counting.StackRealizabilityCountsLoop
import Counting.RealizabilityInitialCountScan

namespace Counting.StackMachine.RealizabilityCheck

def levelRangeSum (nodes : List Executable.Node) (target : Nat) : Nat → List Nat → Nat
  | _,[]=>0
  | start,value::values=>levelContribution (nodes[start]?.getD default) target value+
      levelRangeSum nodes target (start+1) values

theorem level_total_size (node : Executable.Node) (target total value : Nat) :
    (total+levelContribution node target value).size ≤ total.size+value.size+1:=by
  have sum:=nat_add_size_le total value
  by_cases selected : node.level=target
  · simpa only [levelContribution,if_pos selected] using sum
  · simp only [levelContribution,if_neg selected,Nat.add_zero]
    omega

theorem levelRangeSum_eq_map_range (nodes : List Executable.Node) (target start : Nat)
    (values : List Nat) : levelRangeSum nodes target start values=
      ((List.range values.length).map (fun offset=>
        levelContribution (nodes[start+offset]?.getD default) target (values[offset]?.getD 0))).sum:=by
  induction values generalizing start with
  | nil=>simp [levelRangeSum]
  | cons value values ih=>
    rw [levelRangeSum,ih]
    simp only [List.length_cons,List.range_succ_eq_map,List.map_cons,List.map_map,List.sum_cons,
      Nat.add_zero,List.getElem?_cons_zero,Option.getD_some]
    congr 1
    apply congrArg List.sum
    apply List.map_congr_left
    intro offset _
    simp only [Function.comp_apply,List.getElem?_cons_succ]
    rw [show start+1+offset=start+(offset+1) by omega]

theorem levelRangeSum_hidden (vista : Executable.Vista) (weights : Array Nat) (N r : Nat)
    (length : weights.size=vista.nodes.size) :
    N-levelRangeSum vista.nodes.toList (r+1) 0 weights.toList=
      RealizabilityVerifier.hidden N vista weights r:=by
  rw [levelRangeSum_eq_map_range,RealizabilityVerifier.hidden_scan]
  simp only [Array.length_toList,length,Nat.zero_add]
  apply congrArg (fun total=>N-total)
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
