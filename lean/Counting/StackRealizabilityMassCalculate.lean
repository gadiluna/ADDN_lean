import Counting.StackRealizabilityMassPrepare
import Counting.StackRealizabilityMassBounds

namespace Counting.StackMachine.RealizabilityCheck
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

/-- The three compact mass sums use actual preserved scans and binary
arithmetic. The query-plus-one parent code is calculated internally. -/
def massCalculate : Routine 40 := sequence massPrepare
  (sequence massChild (sequence massSupply
    (sequence massKeepSupply (sequence massDemand (clear 25)))))

theorem massCalculate_executes (source weights : List Bool) (accepted : Bool) (tail : List Bool)
    (nodes : List Executable.Node) (sorted : ∀node∈nodes,Executable.countsSorted node.incoming=true)
    (values : List Nat) (length : values.length=nodes.length) (nodeSuffix weightSuffix : List Bool)
    (nodeInput : source=(Encoding.list Encoding.node).encode nodes++nodeSuffix)
    (weightInput : weights=(Encoding.list Encoding.natural).encode values++weightSuffix)
    (target old : Nat) :
    ∃ time ≤ 100000000*(source.length+weights.length+target.size+old.size+2)^15,
      Executes massCalculate (massFile source weights target.bits [] old.bits (accepted::tail) [] [] []) time
        (massFile source weights target.bits [] old.bits (accepted::tail)
          (childRangeSum nodes target old 0 values).bits
          (demandRangeSum nodes target old 0 values).bits
          (supplyRangeSum nodes target old 0 values).bits) := by
  let children := childRangeSum nodes target old 0 values
  let supplied := supplyRangeSum nodes target old 0 values
  let demanded := demandRangeSum nodes target old 0 values
  obtain ⟨prepareTime,prepareBound,preparing⟩ := massPrepare_executes source weights target.bits
    (accepted::tail) [] [] [] old
  obtain ⟨childTime,childBound,childRun⟩ := massChild_executes source weights old.bits [] accepted tail
    nodes values length nodeSuffix weightSuffix nodeInput weightInput target old 0
  obtain ⟨supplyTime,supplyBound,supplyRun⟩ := massSupply_executes source weights old.bits children.bits []
    accepted tail nodes values length nodeSuffix weightSuffix nodeInput weightInput target old 0
  obtain ⟨keepTime,keepBound,keeping⟩ := massKeepSupply_executes source weights target.bits
    (accepted::tail) children.bits old supplied
  obtain ⟨demandTime,demandBound,demandRun⟩ := massDemand_executes source weights old.bits children.bits supplied.bits
    accepted tail nodes sorted values length nodeSuffix weightSuffix nodeInput weightInput target old 0
  simp only [Nat.zero_bits,Nat.size_zero,Nat.zero_add,Nat.add_zero] at childBound childRun supplyBound supplyRun demandBound demandRun
  let ready := massFile source weights target.bits old.bits old.bits (accepted::tail)
    children.bits demanded.bits supplied.bits
  have clearing := clear_executes (25:Fin 42) ready
  have oldAt : ready 25=old.bits := by simp [ready,massFile]
  rw [oldAt,Encoding.bits_length] at clearing
  have final : Function.update ready 25 []=
      massFile source weights target.bits [] old.bits (accepted::tail) children.bits demanded.bits supplied.bits := by
    funext r
    fin_cases r <;> simp [ready,massFile]
  rw [final] at clearing
  have successorSize : (old+1).size ≤ old.size+1 := by
    have bound := DagValidation.increment_length_le old.bits
    simpa only [Machine.increment_bits,Encoding.bits_length] using bound
  let S := source.length+weights.length+target.size+old.size+2
  have positive : 1 ≤ S := by dsimp only [S];omega
  have base : source.length+weights.length+target.size+(old+1).size+1 ≤ S := by dsimp only [S];omega
  have simpleBase : source.length+weights.length+target.size+old.size+1 ≤ S := by dsimp only [S];omega
  have childLimit : childTime ≤ 15000*S^15 := childBound.trans
    (Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left base 5).trans (Nat.pow_le_pow_right positive (by decide))))
  have supplyLimit : supplyTime ≤ 1800000*S^15 := supplyBound.trans
    (Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left base 9).trans (Nat.pow_le_pow_right positive (by decide))))
  have demandLimit : demandTime ≤ 94000000*S^15 := demandBound.trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left simpleBase 15))
  have nodeSequence : (Encoding.sequence Encoding.node nodes).length ≤ source.length := by
    rw [nodeInput]
    change _ ≤ ((Encoding.natural.encode nodes.length++Encoding.sequence Encoding.node nodes)++nodeSuffix).length
    simp only [List.length_append]
    omega
  have nodeBound (node : Executable.Node) (member : node∈nodes) : (Encoding.node.encode node).length ≤ source.length :=
    (DagValidation.node_sequence_member_le nodes node member).trans nodeSequence
  have count := (DagValidation.node_sequence_count_le nodes).trans nodeSequence
  have weightSequence : (Encoding.sequence Encoding.natural values).length ≤ weights.length := by
    rw [weightInput]
    change _ ≤ ((Encoding.natural.encode values.length++Encoding.sequence Encoding.natural values)++weightSuffix).length
    simp only [List.length_append]
    omega
  have suppliedBits := supplyRangeSum_size nodes target old 0 0 values (by omega) source.length nodeBound
  simp only [Nat.zero_add,Nat.size_zero] at suppliedBits
  have sourceS : source.length ≤ S := by dsimp only [S];omega
  have weightsS : weights.length ≤ S := by dsimp only [S];omega
  have valuesS : values.length ≤ S := by omega
  have suppliedLimit : supplied.size ≤ S+S^2 := by
    have product := Nat.mul_le_mul valuesS sourceS
    rw [←pow_two] at product
    dsimp only [supplied]
    omega
  have oldLimit : old.size ≤ S := by dsimp only [S];omega
  have linear : S ≤ S^15 := Nat.le_self_pow (by decide) _
  have square : S^2 ≤ S^15 := Nat.pow_le_pow_right positive (by decide)
  have one : 1 ≤ S^15 := Nat.one_le_pow _ _ positive
  have execution := preparing.sequence (childRun.sequence (supplyRun.sequence
    (keeping.sequence (demandRun.sequence clearing))))
  exact ⟨_,by change _ ≤ 100000000*S^15;omega,execution⟩

end Counting.StackMachine.RealizabilityCheck
