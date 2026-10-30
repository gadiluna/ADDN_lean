import Counting.DagSemanticsTransport
import Counting.ExecutableRefinementAnchor

namespace Counting.Executable
open Counting.TimingProtocolLocal
open scoped BigOperators

theorem sum_decoded_weights (vista : Vista) (valid : vista.valid = true) (weights : Array Nat) (r : Nat) :
    (∑ H ∈ decodedLevel vista r, decodedWeight vista weights r H) =
      ((levelNodes vista r).map (fun i => weights[i]?.getD 0)).sum := by
  rw [sum_decodedLevel vista valid]
  apply congrArg List.sum
  apply List.map_congr_left
  intro i hi
  exact decodedWeight_decode vista valid weights r i hi

theorem sum_decoded_leader_weights (vista : Vista) (valid : vista.valid = true)
    (weights : Array Nat) (r : Nat) :
    (∑ H ∈ (decodedLevel vista r).filter (fun H => input r H = true), decodedWeight vista weights r H) =
      ((levelNodes vista r).map (fun i => if (vista.node i).leader then weights[i]?.getD 0 else 0)).sum := by
  classical
  rw [Finset.sum_filter, sum_decodedLevel vista valid]
  apply congrArg List.sum
  apply List.map_congr_left
  intro i hi
  have info := (mem_levelNodes vista r i).mp hi
  rw [input_decode vista valid r i info.1 info.2, decodedWeight_decode vista valid weights r i hi]

theorem sum_decoded_red_weights (vista : Vista) (valid : vista.valid = true)
    (weights : Array Nat) (r old : Nat) (present : old ∈ levelNodes vista r) :
    (∑ H ∈ decodedLevel vista (r + 1), red r (decodeNode vista r old) H *
      decodedWeight vista weights (r + 1) H) =
      ((levelNodes vista (r + 1)).map (fun i => countFrom (vista.node i) old * weights[i]?.getD 0)).sum := by
  rw [sum_decodedLevel vista valid]
  apply congrArg List.sum
  apply List.map_congr_left
  intro i hi
  have oldInfo := (mem_levelNodes vista r old).mp present
  have info := (mem_levelNodes vista (r + 1) i).mp hi
  rw [red_decode vista valid r old i oldInfo.1 info.1 oldInfo.2 info.2,
    decodedWeight_decode vista valid weights (r + 1) i hi]

theorem sum_decoded_degree_weights (vista : Vista) (valid : vista.valid = true)
    (weights : Array Nat) (r old : Nat) (present : old ∈ levelNodes vista r) :
    (∑ H ∈ decodedLevel vista (r + 1), if parent r H = decodeNode vista r old then
      degree r H * decodedWeight vista weights (r + 1) H else 0) =
      ((children vista old (r + 1)).map (fun i => (vista.node i).degree * weights[i]?.getD 0)).sum := by
  classical
  rw [sum_decodedLevel vista valid, children, list_sum_filter_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro i hi
  simp only [parent_decode_eq_iff vista valid r old i present hi,
    degree_decode, decodedWeight_decode vista valid weights (r + 1) i hi, beq_iff_eq]

theorem nodeAnchorSolution_of_intrinsic (vista : Vista) (valid : vista.valid = true)
    (leaders r : Nat) (z : Counting.FullHistory (r + 1) → ℚ)
    (solution : AnchorSolution leaders r (decodedLevel vista) z) :
    NodeAnchorSolution vista (r + 1) leaders (fun i => z (decodeNode vista (r + 1) i)) := by
  classical
  constructor
  · intro old present
    have oldPresent : old ∈ levelNodes vista r := by simpa only [Nat.add_sub_cancel] using present
    have oldInfo := (mem_levelNodes vista r old).mp oldPresent
    have equation := solution.1 (decodeNode vista r old)
      ((mem_decodedLevel vista r _).mpr ⟨old, oldInfo.1, oldInfo.2, rfl⟩)
    rw [sum_decodedLevel vista valid, sum_decodedLevel vista valid] at equation
    convert equation using 1
    · apply congrArg List.sum
      apply List.map_congr_left
      intro i hi
      have info := (mem_levelNodes vista (r + 1) i).mp hi
      rw [red_decode vista valid r old i oldInfo.1 info.1 oldInfo.2 info.2]
    · apply congrArg List.sum
      apply List.map_congr_left
      intro i hi
      simp only [parent_decode_eq_iff vista valid r old i oldPresent hi, degree_decode]
  · have equation := solution.2
    rw [Finset.sum_filter, sum_decodedLevel vista valid] at equation
    convert equation using 1
    apply congrArg List.sum
    apply List.map_congr_left
    intro i hi
    have info := (mem_levelNodes vista (r + 1) i).mp hi
    rw [input_decode vista valid (r + 1) i info.1 info.2]

/-- Every accepting run of the actual five-step audit supplies the full
intrinsic certificate, including uniqueness of the rational anchor solution. -/
theorem AuditExtracted.toFullCertificate {vista : Vista} {leaders candidate last r : Nat}
    {weights : Array Nat} {values : Array ℚ} {natural : Array Nat}
    (evidence : AuditExtracted vista leaders candidate last ⟨r + 1, weights⟩ values natural) :
    FullCertificate leaders candidate last r (decodedLevel vista) (decodedWeight vista weights) := by
  classical
  obtain ⟨valid, leadersPositive, _, lastPositive, within, anchorPositive, anchorWithin,
    anchorFlat, maximal, _⟩ := evidence.basic
  refine {
    leader_positive := leadersPositive
    anchor_positive := anchorPositive
    anchor_le_final := anchorWithin
    anchor_candidate_positive := ?_
    anchor_leader_candidate := ?_
    anchor_total := ?_
    parent_visible := ?_
    children_nonempty := ?_
    backward := ?_
    candidate_flow := ?_
    suffix_nonflat := ?_
    suffix_audit := ?_
    initial_leader := ?_
    node_bound := ?_
    anchor_flat := ?_
    anchor_unique := ?_ }
  · intro H hH
    obtain ⟨i, hi, li, rfl⟩ := (mem_decodedLevel vista (r + 1) H).mp hH
    have present := (mem_levelNodes vista (r + 1) i).mpr ⟨hi, li⟩
    rw [decodedWeight_decode vista valid weights (r + 1) i present]
    exact evidence.anchor_positive_weights i present
  · rw [sum_decoded_leader_weights vista valid]
    exact evidence.anchor_leader_weights
  · rw [sum_decoded_weights vista valid]
    exact evidence.anchor_total_weights
  · intro k _ H hH
    exact decoded_parent_visible vista valid k H hH
  · intro k hk H hH
    obtain ⟨i, hi, li, rfl⟩ := (mem_decodedLevel vista k H).mp hH
    have present := (mem_levelNodes vista k i).mpr ⟨hi, li⟩
    have check := List.all_eq_true.mp
      (List.all_eq_true.mp evidence.childrenPresent k (List.mem_range.mpr hk)) i present
    apply Finset.card_pos.mp
    rw [decoded_children_card vista valid k i present]
    have nonempty : children vista i (k + 1) ≠ [] := by intro empty; simp [empty] at check
    exact List.length_pos_iff.mpr nonempty
  · intro k hk H hH
    obtain ⟨i, hi, li, rfl⟩ := (mem_decodedLevel vista k H).mp hH
    have present := (mem_levelNodes vista k i).mpr ⟨hi, li⟩
    rw [sum_decoded_children vista valid weights k i present,
      decodedWeight_decode vista valid weights k i present]
    have equation := propagateWeights_backward vista (r + 1) natural k hk i present
    rw [← evidence.weights] at equation
    exact equation.symm
  · intro k hk H hH
    obtain ⟨i, hi, li, rfl⟩ := (mem_decodedLevel vista k H).mp hH
    have present := (mem_levelNodes vista k i).mpr ⟨hi, li⟩
    rw [sum_decoded_degree_weights vista valid weights k i present,
      sum_decoded_red_weights vista valid weights k i present]
    exact (evidence.all_flow k hk i present).symm
  · intro k hk kl flatAll
    have noFlat := maximal (k + 1) (by dsimp at hk ⊢; omega) (by omega)
    have nonempty := levelNodes_nonempty_of_le vista valid k (by omega)
    have actualFlat : flat vista (k + 1) = true := by
      simp only [flat, Bool.and_eq_true, decide_eq_true_eq, Nat.add_sub_cancel]
      refine ⟨⟨by omega, ?_⟩, ?_⟩
      · cases h : levelNodes vista k with
        | nil => exact False.elim (nonempty h)
        | cons head rest => rfl
      · apply List.all_eq_true.mpr
        intro i hi
        have info := (mem_levelNodes vista k i).mp hi
        have equal := flatAll (decodeNode vista k i)
          ((mem_decodedLevel vista k _).mpr ⟨i, info.1, info.2, rfl⟩)
        rw [decoded_children_card vista valid k i hi] at equal
        exact beq_iff_eq.mpr equal
    rw [actualFlat] at noFlat
    contradiction
  · intro H hH
    obtain ⟨i, hi, li, rfl⟩ := (mem_decodedLevel vista (r + 1) H).mp hH
    have present := (mem_levelNodes vista (r + 1) i).mpr ⟨hi, li⟩
    rw [decoded_descendants_card vista valid (r + 1) last i anchorWithin present,
      decodedWeight_decode vista valid weights (r + 1) i present]
    exact of_decide_eq_true (List.all_eq_true.mp evidence.suffixCheck i present)
  · obtain ⟨i, hi, leader⟩ := List.any_eq_true.mp evidence.leaderSeen
    have info := (mem_levelNodes vista 0 i).mp hi
    refine ⟨decodeNode vista 0 i, (mem_decodedLevel vista 0 _).mpr ⟨i, info.1, info.2, rfl⟩, ?_⟩
    exact (input_decode vista valid 0 i info.1 info.2).trans leader
  · intro k hk
    rw [decodedLevel_eq_levels vista valid, ← levelNodes_length_eq_visible_card vista valid]
    exact of_decide_eq_true (List.all_eq_true.mp evidence.bounded k (List.mem_range.mpr (by omega)))
  · intro H hH
    obtain ⟨i, hi, li, rfl⟩ := (mem_decodedLevel vista r H).mp hH
    have present := (mem_levelNodes vista r i).mpr ⟨hi, li⟩
    rw [decoded_children_card vista valid r i present]
    have checks := anchorFlat
    simp only [flat, Bool.and_eq_true, Nat.add_sub_cancel] at checks
    exact beq_iff_eq.mp (List.all_eq_true.mp checks.2 i present)
  · intro z solution H hH
    obtain ⟨i, hi, li, rfl⟩ := (mem_decodedLevel vista (r + 1) H).mp hH
    have present := (mem_levelNodes vista (r + 1) i).mpr ⟨hi, li⟩
    rw [decodedWeight_decode vista valid weights (r + 1) i present]
    exact evidence.anchor_unique (fun i => z (decodeNode vista (r + 1) i))
      (nodeAnchorSolution_of_intrinsic vista valid leaders r z solution) i present

theorem audit_pass (vista : Vista) (leaders candidate last : Nat) (witness : AuditWitness)
    (accepted : audit? vista leaders candidate last = some witness) :
    Pass leaders candidate last (vista.node vista.bottom).level vista.denotes := by
  obtain ⟨values, natural, evidence⟩ := audit_extract vista leaders candidate last witness accepted
  have valid := evidence.basic.1
  have positive := evidence.basic.2.2.2.2.2.1
  rcases witness with ⟨anchor, weights⟩
  cases anchor with
  | zero => simp only at positive; omega
  | succ r =>
      refine ⟨r, decodedWeight vista weights, ⟨?_⟩⟩
      have certificate := evidence.toFullCertificate
      have visible : decodedLevel vista = levels (vista.node vista.bottom).level vista.denotes := by
        funext k
        exact decodedLevel_eq_levels vista valid k
      rw [visible] at certificate
      exact certificate

end Counting.Executable
