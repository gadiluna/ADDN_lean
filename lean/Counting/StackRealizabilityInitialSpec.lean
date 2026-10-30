import Counting.StackRealizabilityInitialItem
import Counting.StackRealizabilityCountsLoop
import Counting.RealizabilityInitialCountScan

namespace Counting.StackMachine.RealizabilityCheck

def initialRangeSum (nodes : List Executable.Node) (leader : Bool) : Nat → List Nat → Nat
  | _,[]=>0
  | start,value::values=>initialContribution (nodes[start]?.getD default) leader value+
      initialRangeSum nodes leader (start+1) values

theorem initial_totals_size (node : Executable.Node) (leaders nonleaders value : Nat) :
    (leaders+initialContribution node true value).size+
      (nonleaders+initialContribution node false value).size≤leaders.size+nonleaders.size+value.size+1:=by
  have first:=nat_add_size_le leaders value
  have second:=nat_add_size_le nonleaders value
  by_cases level : node.level=0
  · cases label:node.leader <;> simp [initialContribution,level,label] <;> omega
  · simp only [initialContribution,level,false_and,if_false,Nat.add_zero]
    omega

theorem initialRangeSum_eq_map_range (nodes : List Executable.Node) (leader : Bool) (start : Nat)
    (values : List Nat) : initialRangeSum nodes leader start values=
      ((List.range values.length).map (fun offset=>
        initialContribution (nodes[start+offset]?.getD default) leader (values[offset]?.getD 0))).sum:=by
  induction values generalizing start with
  | nil=>simp [initialRangeSum]
  | cons value values ih=>
    rw [initialRangeSum,ih]
    simp only [List.length_cons,List.range_succ_eq_map,List.map_cons,List.map_map,List.sum_cons,
      Nat.add_zero,List.getElem?_cons_zero,Option.getD_some]
    congr 1
    apply congrArg List.sum
    apply List.map_congr_left
    intro offset _
    simp only [Function.comp_apply,List.getElem?_cons_succ]
    rw [show start+1+offset=start+(offset+1) by omega]

theorem initialRangeSum_vista (vista : Executable.Vista) (weights : Array Nat) (leader : Bool)
    (length : weights.size=vista.nodes.size) :
    initialRangeSum vista.nodes.toList leader 0 weights.toList=
      RealizabilityVerifier.initialCount vista weights leader:=by
  rw [initialRangeSum_eq_map_range,RealizabilityVerifier.initialCount_scan]
  simp only [Array.length_toList,length,Nat.zero_add]
  apply congrArg List.sum
  apply List.map_congr_left
  intro index member
  have nodeInside : index<vista.nodes.size:=List.mem_range.mp member
  have weightInside : index<weights.size:=by omega
  have nodeList : index<vista.nodes.toList.length:=by simpa only [Array.length_toList] using nodeInside
  have weightList : index<weights.toList.length:=by simpa only [Array.length_toList] using weightInside
  simp only [initialContribution,List.getElem?_eq_getElem nodeList,List.getElem?_eq_getElem weightList,
    Option.getD_some,Array.getElem_toList,Executable.Vista.node,Array.getElem?_eq_getElem nodeInside,
    RealizabilityVerifier.weight,Array.getElem?_eq_getElem weightInside]

end Counting.StackMachine.RealizabilityCheck
