import Counting.StackRealizabilityMassBounds
import Counting.StackRealizabilityChildSpec

namespace Counting.StackMachine.RealizabilityCheck

theorem childRangeSum_size (nodes : List Executable.Node) (target old start total : Nat)
    (values : List Nat) :
    (total+childRangeSum nodes target old start values).size ≤
      total.size+(Encoding.sequence Encoding.natural values).length := by
  induction values generalizing start total with
  | nil => simp [childRangeSum,Encoding.sequence]
  | cons value values ih =>
    let node := nodes[start]?.getD default
    let nextTotal := total+childContribution node target old value
    have nextSize := child_total_size node target old total value
    have tailBound := ih (start+1) nextTotal
    simp only [childRangeSum,←Nat.add_assoc]
    change (nextTotal+childRangeSum nodes target old (start+1) values).size ≤ _
    simp only [Encoding.sequence,List.length_append,Encoding.natural_length]
    dsimp only [nextTotal] at tailBound ⊢
    omega

def massInputSize (nodes : List Executable.Node) (values : List Nat) : Nat :=
  ((Encoding.list Encoding.node).encode nodes).length+
  ((Encoding.list Encoding.natural).encode values).length+1

theorem massInputSize_positive (nodes : List Executable.Node) (values : List Nat) :
    1 ≤ massInputSize nodes values := by unfold massInputSize;omega

theorem naturalPayload_size_le_sequence (values : List Nat) (index : Nat) :
    (values[index]?.getD 0).size ≤ (Encoding.sequence Encoding.natural values).length := by
  induction values generalizing index with
  | nil => simp [Encoding.sequence]
  | cons value values ih =>
    cases index with
    | zero => simp [Encoding.sequence,Encoding.natural_length];omega
    | succ index =>
      have tail := ih index
      simp only [List.getElem?_cons_succ,Encoding.sequence,List.length_append,Encoding.natural_length]
      omega

/-- Every intermediate sum fits quadratically in the two explicit input
lists, independent of the magnitudes represented by their binary labels. -/
theorem massRangeSums_size (nodes : List Executable.Node) (values : List Nat)
    (length : values.length=nodes.length)
    (sorted : ∀node∈nodes,Executable.countsSorted node.incoming=true) (target old : Nat) :
    (childRangeSum nodes target old 0 values).size ≤ 2*(massInputSize nodes values)^2 ∧
    (supplyRangeSum nodes target old 0 values).size ≤ 2*(massInputSize nodes values)^2 ∧
    (demandRangeSum nodes target old 0 values).size ≤ 2*(massInputSize nodes values)^2 := by
  let S := massInputSize nodes values
  let B := ((Encoding.list Encoding.node).encode nodes).length
  have nodeSequence : (Encoding.sequence Encoding.node nodes).length ≤ B := by
    change _ ≤ (Encoding.natural.encode nodes.length++Encoding.sequence Encoding.node nodes).length
    simp only [List.length_append]
    omega
  have bounded (node : Executable.Node) (member : node∈nodes) : (Encoding.node.encode node).length ≤ B :=
    (DagValidation.node_sequence_member_le nodes node member).trans nodeSequence
  have weightSequence : (Encoding.sequence Encoding.natural values).length ≤ S := by
    change _ ≤ ((Encoding.list Encoding.node).encode nodes).length+
      (Encoding.natural.encode values.length++Encoding.sequence Encoding.natural values).length+1
    simp only [List.length_append]
    omega
  have count : values.length ≤ S := by
    have number := (DagValidation.node_sequence_count_le nodes).trans nodeSequence
    dsimp only [S,massInputSize,B] at *
    omega
  have boundS : B ≤ S := by dsimp only [B,S,massInputSize];omega
  have child := childRangeSum_size nodes target old 0 0 values
  have supply := supplyRangeSum_size nodes target old 0 0 values (by omega) B bounded
  have demand := demandRangeSum_size nodes target old 0 0 values (by omega) B bounded sorted
  simp only [Nat.zero_add,Nat.size_zero] at child supply demand
  have product : values.length*B ≤ S^2 := by simpa only [pow_two] using Nat.mul_le_mul count boundS
  have linear : S ≤ S^2 := Nat.le_self_pow (by decide) _
  change _ ≤ 2*S^2 ∧ _ ≤ 2*S^2 ∧ _ ≤ 2*S^2
  omega

end Counting.StackMachine.RealizabilityCheck
