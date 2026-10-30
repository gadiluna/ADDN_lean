import Counting.StackRealizabilityDemandNodeSpec
import Counting.StackRealizabilitySupplySpec
import Counting.StackRealizabilityLevelSpec

namespace Counting.StackMachine.RealizabilityCheck

/-- The already serialized weights pay for each addition; the explicit
node table bounds the degree of every multiplication operand. -/
theorem supplyRangeSum_size (nodes : List Executable.Node) (target old start total : Nat)
    (values : List Nat) (inside : start+values.length ≤ nodes.length) (B : Nat)
    (bounded : ∀ node∈nodes,(Encoding.node.encode node).length ≤ B) :
    (total+supplyRangeSum nodes target old start values).size ≤
      total.size+(Encoding.sequence Encoding.natural values).length+values.length*B:=by
  induction values generalizing start total with
  | nil=>simp [supplyRangeSum,Encoding.sequence]
  | cons value values ih=>
    have indexBound : start<nodes.length:=by simp only [List.length_cons] at inside;omega
    let node:=nodes[start]
    have selected : nodes[start]?.getD default=node:=by simp [node,indexBound]
    have degreeBound : node.degree.size ≤ B:=by
      have fields:=node_supply_fields_size node
      have code:=bounded node (List.getElem_mem indexBound)
      omega
    let nextTotal:=total+supplyContribution node target old value
    have nextSize:=supply_total_size node target old total value
    have tailBound:=ih (start+1) nextTotal (by simp only [List.length_cons] at inside;omega)
    simp only [supplyRangeSum,selected,←Nat.add_assoc]
    change (nextTotal+supplyRangeSum nodes target old (start+1) values).size ≤ _
    simp only [Encoding.sequence,List.length_append,Encoding.natural_length,List.length_cons,Nat.add_mul,Nat.one_mul]
    dsimp only [nextTotal] at tailBound ⊢
    omega

theorem demandRangeSum_size (nodes : List Executable.Node) (target old start total : Nat)
    (values : List Nat) (inside : start+values.length ≤ nodes.length) (B : Nat)
    (bounded : ∀ node∈nodes,(Encoding.node.encode node).length ≤ B)
    (sorted : ∀ node∈nodes,Executable.countsSorted node.incoming=true) :
    (total+demandRangeSum nodes target old start values).size ≤
      total.size+(Encoding.sequence Encoding.natural values).length+values.length*B:=by
  induction values generalizing start total with
  | nil=>simp [demandRangeSum,Encoding.sequence]
  | cons value values ih=>
    have indexBound : start<nodes.length:=by simp only [List.length_cons] at inside;omega
    let node:=nodes[start]
    have selected : nodes[start]?.getD default=node:=by simp [node,indexBound]
    have member : node∈nodes:=List.getElem_mem indexBound
    have code:=bounded node member
    let nextTotal:=total+demandEdges node.level target old value node.incoming
    have nextSize:=demandNode_total_size node target old total value (sorted node member)
    have tailBound:=ih (start+1) nextTotal (by simp only [List.length_cons] at inside;omega)
    simp only [demandRangeSum,selected,←Nat.add_assoc]
    change (nextTotal+demandRangeSum nodes target old (start+1) values).size ≤ _
    simp only [Encoding.sequence,List.length_append,Encoding.natural_length,List.length_cons,Nat.add_mul,Nat.one_mul]
    dsimp only [nextTotal] at tailBound ⊢
    omega

theorem levelRangeSum_size (nodes : List Executable.Node) (target start total : Nat)
    (values : List Nat) :
    (total+levelRangeSum nodes target start values).size ≤
      total.size+(Encoding.sequence Encoding.natural values).length:=by
  induction values generalizing start total with
  | nil=>simp [levelRangeSum,Encoding.sequence]
  | cons value values ih=>
    let node:=nodes[start]?.getD default
    let nextTotal:=total+levelContribution node target value
    have nextSize:=level_total_size node target total value
    have tailBound:=ih (start+1) nextTotal
    simp only [levelRangeSum,←Nat.add_assoc]
    change (nextTotal+levelRangeSum nodes target (start+1) values).size ≤ _
    simp only [Encoding.sequence,List.length_append,Encoding.natural_length]
    dsimp only [nextTotal] at tailBound ⊢
    omega

end Counting.StackMachine.RealizabilityCheck
