import Counting.StackRealizabilityDemandItem
import Counting.StackRealizabilityCountsLoop
import Counting.RealizabilityInitialCountScan
import Counting.EncodingRecognitionBounds

namespace Counting.StackMachine.RealizabilityCheck

def demandRangeSum (nodes : List Executable.Node) (target old : Nat) : Nat → List Nat → Nat
  | _,[]=>0
  | start,value::values=>demandEdges (nodes[start]?.getD default).level target old value
      (nodes[start]?.getD default).incoming+demandRangeSum nodes target old (start+1) values

theorem demandNode_total_size (node : Executable.Node) (target old total value : Nat)
    (sorted : Executable.countsSorted node.incoming=true) :
    (total+demandEdges node.level target old value node.incoming).size ≤
      total.size+value.size+(Encoding.node.encode node).length+1:=by
  rw [demandEdges_node node target old value sorted]
  have sum:=nat_add_size_le total (value*Executable.countFrom node old)
  have product:=NaturalCall.product_bits_length value.bits (Executable.countFrom node old).bits
  simp only [Encoding.value_bits,Encoding.bits_length] at product
  have count:=Encoding.redBits_le_node node old
  rw [←Encoding.node_length] at count
  by_cases selected : node.level=target
  · rw [if_pos selected];omega
  · rw [if_neg selected,Nat.add_zero];omega

theorem demandRangeSum_eq_map_range (nodes : List Executable.Node) (target old start : Nat)
    (values : List Nat) : demandRangeSum nodes target old start values=
      ((List.range values.length).map (fun offset=>
        demandEdges (nodes[start+offset]?.getD default).level target old (values[offset]?.getD 0)
          (nodes[start+offset]?.getD default).incoming)).sum:=by
  induction values generalizing start with
  | nil=>simp [demandRangeSum]
  | cons value values ih=>
    rw [demandRangeSum,ih]
    simp only [List.length_cons,List.range_succ_eq_map,List.map_cons,List.map_map,List.sum_cons,
      Nat.add_zero,List.getElem?_cons_zero,Option.getD_some]
    congr 1
    apply congrArg List.sum
    apply List.map_congr_left
    intro offset _
    simp only [Function.comp_apply,List.getElem?_cons_succ]
    rw [show start+1+offset=start+(offset+1) by omega]

theorem demandRangeSum_vista (vista : Executable.Vista) (weights : Array Nat) (r old : Nat)
    (length : weights.size=vista.nodes.size)
    (sorted : ∀ i,i<vista.nodes.size → Executable.countsSorted (vista.node i).incoming=true) :
    demandRangeSum vista.nodes.toList (r+1) old 0 weights.toList=
      RealizabilityVerifier.demand vista weights r old:=by
  rw [demandRangeSum_eq_map_range,RealizabilityVerifier.demand_scan]
  simp only [Array.length_toList,length,Nat.zero_add]
  apply congrArg List.sum
  apply List.map_congr_left
  intro index member
  have nodeInside : index<vista.nodes.size:=List.mem_range.mp member
  have weightInside : index<weights.size:=by omega
  have nodeList : index<vista.nodes.toList.length:=by simpa only [Array.length_toList] using nodeInside
  have weightList : index<weights.toList.length:=by simpa only [Array.length_toList] using weightInside
  simp only [List.getElem?_eq_getElem nodeList,List.getElem?_eq_getElem weightList,
    Option.getD_some,Array.getElem_toList]
  have nodeAt : vista.node index=vista.nodes[index]:=by
    simp only [Executable.Vista.node,Array.getElem?_eq_getElem nodeInside,Option.getD_some]
  rw [demandEdges_node _ _ _ _ (by simpa only [nodeAt] using sorted index nodeInside)]
  simp only [nodeAt,RealizabilityVerifier.weight,Array.getElem?_eq_getElem weightInside,Option.getD_some]

end Counting.StackMachine.RealizabilityCheck
