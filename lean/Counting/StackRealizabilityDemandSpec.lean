import Counting.StackRealizabilityDemandEdge
import Counting.StackRealizabilityCountsLoop
import Counting.RealizabilityDemandScan

namespace Counting.StackMachine.RealizabilityCheck

def demandEdges (level target old value : Nat) : List (Nat×Nat) → Nat
  | []=>0
  | edge::edges=>demandContribution level target edge.1 old value edge.2+demandEdges level target old value edges

theorem demand_total_size (level target source old value count total : Nat) :
    (total+demandContribution level target source old value count).size ≤ total.size+value.size+count.size+1:=by
  have sum:=nat_add_size_le total (value*count)
  have product:=NaturalCall.product_bits_length value.bits count.bits
  simp only [Encoding.value_bits,Encoding.bits_length] at product
  by_cases selected : level=target ∧ source=old
  · simp only [demandContribution,if_pos selected]
    omega
  · simp only [demandContribution,if_neg selected,Nat.add_zero]
    omega

theorem demandEdges_eq_sum (level target old value : Nat) (edges : List (Nat×Nat)) :
    demandEdges level target old value edges=
      (edges.map (fun edge=>if level=target ∧ edge.1=old then value*edge.2 else 0)).sum:=by
  induction edges with
  | nil=>rfl
  | cons edge edges ih=>simp only [demandEdges,demandContribution,List.map_cons,List.sum_cons,ih]

theorem demandEdges_node (node : Executable.Node) (target old value : Nat)
    (sorted : Executable.countsSorted node.incoming=true) :
    demandEdges node.level target old value node.incoming=
      if node.level=target then value*Executable.countFrom node old else 0:=by
  rw [demandEdges_eq_sum]
  by_cases level : node.level=target
  · simp only [level,true_and,if_true]
    exact (RealizabilityVerifier.weighted_countFrom_sum node old value sorted).symm
  · simp [level]

end Counting.StackMachine.RealizabilityCheck
