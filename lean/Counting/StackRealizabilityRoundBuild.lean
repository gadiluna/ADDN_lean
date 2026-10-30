import Counting.StackRealizabilityRoundCost

namespace Counting.StackMachine.RealizabilityCheck
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8000

def roundBuild : Routine 98 := sequence roundPrepare
  (sequence roundMasks (sequence roundVisible
    (sequence roundPointTables (sequence roundOutside roundIncidences))))

/-- All eight compact graph fields are constructed from the encoded node
and count lists. No field table is supplied as an uncharged oracle. -/
theorem roundBuild_executes (nodes : List Executable.Node) (values : List Nat)
    (length : values.length=nodes.length)
    (sorted : ∀node∈nodes,Executable.countsSorted node.incoming=true)
    (order round : Nat) (accepted : Bool) (tail : List Bool) (extra : Fin 3→List Bool) :
    ∃ time ≤ 100000000000000000000*(roundSize nodes values order round)^16,
      Executes roundBuild (roundFile (roundInputData nodes values order round (accepted::tail) extra)) time
        (roundFile (roundComputedData nodes values order round
          ((accepted && roundNumericValue nodes values order round)::tail) extra)) := by
  let d0 := roundInputData nodes values order round (accepted::tail) extra
  obtain ⟨t0,b0,r0⟩ := roundPrepare_executes d0 round
    (by simp [d0,roundInputData]) (by simp [d0,roundInputData]) (by simp [d0,roundInputData])
  let d1 := Function.update (Function.update d0 4 (round+1).bits) 6 (d0 0)
  obtain ⟨t1,b1,r1⟩ := roundMasks_executes d1 nodes round accepted tail
    (by simp [d1,d0,roundInputData]) (by simp [d1,d0,roundInputData])
    (by simp [d1,d0,roundInputData]) (by simp [d1])
    (by simp [d1,d0,roundInputData]) (by simp [d1,d0,roundInputData])
    (by simp [d1,d0,roundInputData]) (by simp [d1,d0,roundInputData])
  let d2 := roundMasksData d1 nodes round
  obtain ⟨t2,b2,r2⟩ := roundVisible_executes d2 nodes values length (round+1) accepted tail
    (by simp [d2,d1,d0,roundMasksData,roundInputData])
    (by simp [d2,d1,d0,roundMasksData,roundInputData])
    (by simp [d2,d1,roundMasksData]) (by simp [d2,d1,d0,roundMasksData,roundInputData])
    (by simp [d2,d1,d0,roundMasksData,roundInputData])
  let visible := roundVisibleValue nodes values round
  let d3 := Function.update d2 16 visible.bits
  obtain ⟨t3,b3,r3⟩ := roundPointTables_executes d3 nodes values length sorted (round+1) order visible accepted tail
    (by simp [d3,d2,d1,d0,roundMasksData,roundInputData])
    (by simp [d3,d2,d1,d0,roundMasksData,roundInputData])
    (by simp [d3,d2,d1,roundMasksData]) (by simp [d3,d2,d1,d0,roundMasksData,roundInputData])
    (by simp [d3,d2,d1,d0,roundMasksData,roundInputData]) (by simp [d3])
    (by simp [d3,d2,d1,d0,roundMasksData,roundInputData])
    (by simp [d3,d2,d1,d0,roundMasksData,roundInputData])
  let d4 := roundPointTablesData d3 nodes values (round+1) order visible accepted tail
  obtain ⟨t4,b4,r4⟩ := roundOutside_executes d4 order visible
    (by simp [d4,d3,d2,d1,d0,roundPointTablesData,roundMasksData,roundInputData])
    (by simp [d4,d3,roundPointTablesData])
    (by simp [d4,d3,d2,d1,d0,roundPointTablesData,roundMasksData,roundInputData])
  let d5 := Function.update d4 13 (List.replicate ((d4 7).length-1) false++[decide (0<order-visible)])
  obtain ⟨t5,b5,r5⟩ := roundIncidences_executes d5 nodes
    (accepted && roundNumericValue nodes values order round) tail
    (by simp [d5,d4,d3,d2,roundPointTablesData,roundMasksData,roundNumericValue,visible])
    (by simp [d5,d4,d3,d2,roundPointTablesData,roundMasksData])
    (by simp [d5,d4,d3,d2,roundPointTablesData,roundMasksData])
    (by simp [d5,d4,d3,d2,d1,d0,roundPointTablesData,roundMasksData,roundInputData])
    (by simp [d5,d4,d3,d2,d1,d0,roundPointTablesData,roundMasksData,roundInputData])
  have final : roundIncidenceData d5 nodes=roundComputedData nodes values order round
      ((accepted && roundNumericValue nodes values order round)::tail) extra := by
    funext i
    fin_cases i <;> simp [roundIncidenceData,d5,d4,d3,d2,d1,d0,roundComputedData,roundComputedTables,
      roundPointTablesData,roundMasksData,roundInputData,roundNumericValue,visible]
  rw [final] at r5
  simp [d0,roundInputData] at b0
  simp [d1,d0,roundInputData] at b1
  simp [d3,d2,roundMasksData] at b3
  simp [d4,d3,d2,roundPointTablesData,roundMasksData] at b4
  simp [d5,d4,d3,d2,roundPointTablesData,roundMasksData] at b5
  let S := roundSize nodes values order round
  have positive : 1 ≤ S := roundSize_positive nodes values order round
  have visibleSize := roundVisibleValue_size nodes values round
  have successorSize : (round+1).size ≤ round.size+1 :=
    (Nat.size_le_size (Nat.succ_le_of_lt (Nat.lt_size_self round))).trans_eq Nat.size_pow
  have nodeSequence : (Encoding.sequence Encoding.node nodes).length ≤
      ((Encoding.list Encoding.node).encode nodes).length := by
    change _ ≤ (Encoding.natural.encode nodes.length++Encoding.sequence Encoding.node nodes).length
    simp only [List.length_append];omega
  have prepLimit : t0 ≤ 20*S := b0.trans (by dsimp only [S,roundSize,massInputSize];omega)
  have masksBase : ((Encoding.list Encoding.node).encode nodes).length+round.size+(round+1).size+1 ≤ 2*S := by
    dsimp only [S,roundSize,massInputSize];omega
  have masksLimit : t1 ≤ 384000*S^5 := by
    have raw := b1.trans (Nat.mul_le_mul_left 12000 (Nat.pow_le_pow_left masksBase 5))
    exact raw.trans_eq (roundMasks_scale S)
  have visibleBase : massInputSize nodes values+(round+1).size ≤ S := by dsimp only [S,roundSize];omega
  have visibleLimit : t2 ≤ 15000*S^5 := b2.trans
    (Nat.mul_le_mul_left 15000 (Nat.pow_le_pow_left visibleBase 5))
  have pointBase : massInputSize nodes values+(round+1).size+order.size+visible.size+
      (nodes.length+1)+2*(nodes.length+1)+2 ≤ 4*S := by
    change visible.size ≤ massInputSize nodes values at visibleSize
    dsimp only [S,roundSize];omega
  have pointLimit : t3 ≤ 1288490188800000000*S^16 := by
    have raw := b3.trans (Nat.mul_le_mul_left 300000000 (Nat.pow_le_pow_left pointBase 16))
    exact raw.trans_eq (roundPoint_scale S)
  have outsideLimit : t4 ≤ 80*S := by
    change visible.size ≤ massInputSize nodes values at visibleSize
    apply b4.trans
    dsimp only [S,roundSize]
    omega
  have incidenceBase : (Encoding.sequence Encoding.node nodes).length+(nodes.length+1)+2 ≤ S := by
    dsimp only [S,roundSize,massInputSize];omega
  have incidenceLimit : t5 ≤ 50000*S^8 := b5.trans
    (Nat.mul_le_mul_left 50000 (Nat.pow_le_pow_left incidenceBase 8))
  have linear : S ≤ S^16 := Nat.le_self_pow (by decide) _
  have fifth : S^5 ≤ S^16 := Nat.pow_le_pow_right positive (by decide)
  have eighth : S^8 ≤ S^16 := Nat.pow_le_pow_right positive (by decide)
  have one : 1 ≤ S^16 := Nat.one_le_pow _ _ positive
  have execution := r0.sequence (r1.sequence (r2.sequence (r3.sequence (r4.sequence r5))))
  exact ⟨_,by change _ ≤ 100000000000000000000*S^16;omega,execution⟩

end Counting.StackMachine.RealizabilityCheck
