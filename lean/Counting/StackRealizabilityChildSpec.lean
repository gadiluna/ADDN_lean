import Counting.StackRealizabilityChildItem
import Counting.StackRealizabilityCountsLoop
import Counting.RealizabilityInitialCountScan

namespace Counting.StackMachine.RealizabilityCheck

def childRangeSum (nodes : List Executable.Node) (target old : Nat) : Nat → List Nat → Nat
  | _,[]=>0
  | start,value::values=>childContribution (nodes[start]?.getD default) target old value+
      childRangeSum nodes target old (start+1) values

theorem child_total_size (node : Executable.Node) (target old total value : Nat) :
    (total+childContribution node target old value).size ≤ total.size+value.size+1:=by
  have sum:=nat_add_size_le total value
  by_cases selected : node.level=target ∧ node.parent=some old
  · simpa only [childContribution,if_pos selected] using sum
  · simp only [childContribution,if_neg selected,Nat.add_zero]
    omega

theorem childRangeSum_eq_map_range (nodes : List Executable.Node) (target old start : Nat)
    (values : List Nat) : childRangeSum nodes target old start values=
      ((List.range values.length).map (fun offset=>
        childContribution (nodes[start+offset]?.getD default) target old (values[offset]?.getD 0))).sum:=by
  induction values generalizing start with
  | nil=>simp [childRangeSum]
  | cons value values ih=>
    rw [childRangeSum,ih]
    simp only [List.length_cons,List.range_succ_eq_map,List.map_cons,List.map_map,List.sum_cons,
      Nat.add_zero,List.getElem?_cons_zero,Option.getD_some]
    congr 1
    apply congrArg List.sum
    apply List.map_congr_left
    intro offset _
    simp only [Function.comp_apply,List.getElem?_cons_succ]
    rw [show start+1+offset=start+(offset+1) by omega]

theorem childRangeSum_vista (vista : Executable.Vista) (weights : Array Nat) (r old : Nat)
    (length : weights.size=vista.nodes.size) :
    childRangeSum vista.nodes.toList (r+1) old 0 weights.toList=
      RealizabilityVerifier.childCount vista weights r old:=by
  rw [childRangeSum_eq_map_range,RealizabilityVerifier.childCount_scan]
  simp only [Array.length_toList,length,Nat.zero_add]
  apply congrArg List.sum
  apply List.map_congr_left
  intro index member
  have nodeInside : index<vista.nodes.size:=List.mem_range.mp member
  have weightInside : index<weights.size:=by omega
  have nodeList : index<vista.nodes.toList.length:=by simpa only [Array.length_toList] using nodeInside
  have weightList : index<weights.toList.length:=by simpa only [Array.length_toList] using weightInside
  simp only [childContribution,List.getElem?_eq_getElem nodeList,List.getElem?_eq_getElem weightList,
    Option.getD_some,Array.getElem_toList,Executable.Vista.node,Array.getElem?_eq_getElem nodeInside,
    RealizabilityVerifier.weight,Array.getElem?_eq_getElem weightInside]

end Counting.StackMachine.RealizabilityCheck
