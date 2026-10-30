import Counting.StackRealizabilitySupplyItem
import Counting.StackRealizabilityCountsLoop
import Counting.RealizabilityInitialCountScan

namespace Counting.StackMachine.RealizabilityCheck

def supplyRangeSum (nodes : List Executable.Node) (target old : Nat) : Nat → List Nat → Nat
  | _,[]=>0
  | start,value::values=>supplyContribution (nodes[start]?.getD default) target old value+
      supplyRangeSum nodes target old (start+1) values

theorem supply_total_size (node : Executable.Node) (target old total value : Nat) :
    (total+supplyContribution node target old value).size ≤ total.size+value.size+node.degree.size+1:=by
  have sum:=nat_add_size_le total (value*node.degree)
  have product:=NaturalCall.product_bits_length value.bits node.degree.bits
  simp only [Encoding.value_bits,Encoding.bits_length] at product
  by_cases selected : node.level=target ∧ node.parent=some old
  · simp only [supplyContribution,if_pos selected]
    omega
  · simp only [supplyContribution,if_neg selected,Nat.add_zero]
    omega

theorem supplyRangeSum_eq_map_range (nodes : List Executable.Node) (target old start : Nat)
    (values : List Nat) : supplyRangeSum nodes target old start values=
      ((List.range values.length).map (fun offset=>
        supplyContribution (nodes[start+offset]?.getD default) target old (values[offset]?.getD 0))).sum:=by
  induction values generalizing start with
  | nil=>simp [supplyRangeSum]
  | cons value values ih=>
    rw [supplyRangeSum,ih]
    simp only [List.length_cons,List.range_succ_eq_map,List.map_cons,List.map_map,List.sum_cons,
      Nat.add_zero,List.getElem?_cons_zero,Option.getD_some]
    congr 1
    apply congrArg List.sum
    apply List.map_congr_left
    intro offset _
    simp only [Function.comp_apply,List.getElem?_cons_succ]
    rw [show start+1+offset=start+(offset+1) by omega]

theorem supplyRangeSum_vista (vista : Executable.Vista) (weights : Array Nat) (r old : Nat)
    (length : weights.size=vista.nodes.size) :
    supplyRangeSum vista.nodes.toList (r+1) old 0 weights.toList=
      RealizabilityVerifier.supply vista weights r old:=by
  rw [supplyRangeSum_eq_map_range,RealizabilityVerifier.supply_scan]
  simp only [Array.length_toList,length,Nat.zero_add]
  apply congrArg List.sum
  apply List.map_congr_left
  intro index member
  have nodeInside : index<vista.nodes.size:=List.mem_range.mp member
  have weightInside : index<weights.size:=by omega
  have nodeList : index<vista.nodes.toList.length:=by simpa only [Array.length_toList] using nodeInside
  have weightList : index<weights.toList.length:=by simpa only [Array.length_toList] using weightInside
  simp only [supplyContribution,List.getElem?_eq_getElem nodeList,List.getElem?_eq_getElem weightList,
    Option.getD_some,Array.getElem_toList,Executable.Vista.node,Array.getElem?_eq_getElem nodeInside,
    RealizabilityVerifier.weight,Array.getElem?_eq_getElem weightInside]

end Counting.StackMachine.RealizabilityCheck
