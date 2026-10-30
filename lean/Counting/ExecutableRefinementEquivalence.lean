import Counting.ExecutableRefinementCompleteWeights

namespace Counting.Executable
open Counting.TimingProtocolLocal
open scoped BigOperators

theorem fullCertificate_leaders_le_candidate (vista : Vista) (leaders candidate last r : Nat)
    (c : ∀ k, Counting.FullHistory k → Nat)
    (certificate : FullCertificate leaders candidate last r (decodedLevel vista) c) : leaders ≤ candidate := by
  rw [← certificate.anchor_leader_candidate, ← certificate.anchor_total]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun _ _ _ => Nat.zero_le _)

/-- Completeness for all five implemented checks, using the actual Gaussian
solver, integer conversion, anchor search, and descending propagation. -/
theorem fullCertificate_audit (vista : Vista) (valid : vista.valid = true)
    (leaders candidate last r : Nat) (c : ∀ k, Counting.FullHistory k → Nat)
    (certificate : FullCertificate leaders candidate last r (decodedLevel vista) c)
    (within : last ≤ (vista.node vista.bottom).level) :
    ∃ witness, audit? vista leaders candidate last = some witness := by
  classical
  let natural := anchorNatural vista r c
  let values := natural.map (fun n : Nat => (n : ℚ))
  let weights := propagateWeights vista (r + 1) natural
  have anchorWithin := certificate.anchor_le_final
  have lastPositive : 0 < last := by omega
  have leadersLe := fullCertificate_leaders_le_candidate vista leaders candidate last r c certificate
  refine ⟨⟨r + 1, weights⟩, AuditExtracted.accepted (values := values) (natural := natural) ?_⟩
  refine {
    opening := ?_
    leaderSeen := ?_
    bounded := ?_
    childrenPresent := ?_
    anchorFound := fullCertificate_anchor_found vista valid leaders candidate last r c certificate within
    solved := ?_
    naturalExact := fullCertificate_natural vista valid leaders candidate last r c certificate
    total := ?_
    weights := rfl
    flowCheck := ?_
    suffixCheck := ?_ }
  · simp [valid, Nat.ne_of_gt certificate.leader_positive, Nat.not_lt.mpr leadersLe,
      Nat.ne_of_gt lastPositive, Nat.not_lt.mpr within]
  · obtain ⟨H, hH, leader⟩ := certificate.initial_leader
    obtain ⟨i, hi, li, rfl⟩ := (mem_decodedLevel vista 0 H).mp hH
    apply List.any_eq_true.mpr
    refine ⟨i, (mem_levelNodes vista 0 i).mpr ⟨hi, li⟩, ?_⟩
    exact (input_decode vista valid 0 i hi li).symm.trans leader
  · apply List.all_eq_true.mpr
    intro k hk
    apply decide_eq_true_eq.mpr
    rw [levelNodes_length_eq_visible_card vista valid, ← decodedLevel_eq_levels vista valid]
    exact certificate.node_bound k (by have := List.mem_range.mp hk; omega)
  · apply List.all_eq_true.mpr
    intro k hk
    apply List.all_eq_true.mpr
    intro i hi
    have info := (mem_levelNodes vista k i).mp hi
    have hasChild := certificate.children_nonempty k (List.mem_range.mp hk) (decodeNode vista k i)
      ((mem_decodedLevel vista k _).mpr ⟨i, info.1, info.2, rfl⟩)
    have positive := Finset.card_pos.mpr hasChild
    rw [decoded_children_card vista valid k i hi] at positive
    cases h : children vista i (k + 1) with
    | nil => simp [h] at positive
    | cons head rest => rfl
  · exact (fullCertificate_solver vista valid leaders candidate last r c certificate).trans
      (congrArg some (anchorNatural_cast vista r c))
  · change ((levelNodes vista (r + 1)).map (fun i => c (r + 1) (decodeNode vista (r + 1) i))).sum = candidate
    rw [← sum_decodedLevel vista valid]
    exact certificate.anchor_total
  · apply List.all_eq_true.mpr
    intro k hk
    cases k with
    | zero => simp
    | succ k =>
        have nozero : (k + 1 == 0) = false := by simp
        change (k + 1 == 0 || _) = true
        rw [nozero, Bool.false_or]
        apply List.all_eq_true.mpr
        intro i hi
        apply beq_iff_eq.mpr
        exact fullCertificate_flow_weights vista valid leaders candidate last r c certificate k
          (by have := List.mem_range.mp hk; dsimp at this; omega) i
          (by simpa only [Nat.add_sub_cancel] using hi)
  · apply List.all_eq_true.mpr
    intro i hi
    apply decide_eq_true_eq.mpr
    have info := (mem_levelNodes vista (r + 1) i).mp hi
    have suffix := certificate.suffix_audit (decodeNode vista (r + 1) i)
      ((mem_decodedLevel vista (r + 1) _).mpr ⟨i, info.1, info.2, rfl⟩)
    rw [decoded_descendants_card vista valid (r + 1) last i anchorWithin hi] at suffix
    change _ ≤ (propagateWeights vista (r + 1) (anchorNatural vista r c))[i]?.getD 0
    rw [fullCertificate_propagated vista valid leaders candidate last r c certificate (r + 1) (le_refl _) i hi]
    exact suffix

theorem pass_audit (vista : Vista) (valid : vista.valid = true) (leaders candidate last : Nat)
    (within : last ≤ (vista.node vista.bottom).level)
    (passes : Pass leaders candidate last (vista.node vista.bottom).level vista.denotes) :
    ∃ witness, audit? vista leaders candidate last = some witness := by
  obtain ⟨r, c, ⟨certificate⟩⟩ := passes
  have visible : decodedLevel vista = levels (vista.node vista.bottom).level vista.denotes := by
    funext k
    exact decodedLevel_eq_levels vista valid k
  have localCertificate : FullCertificate leaders candidate last r (decodedLevel vista) c := by
    rw [visible]
    exact certificate
  exact fullCertificate_audit vista valid leaders candidate last r c localCertificate within

/-- Exact mathematical meaning of an implemented successful audit. The
level bound is the precondition of both core and short scheduled tests. -/
theorem audit_isSome_iff_pass (vista : Vista) (valid : vista.valid = true) (leaders candidate last : Nat)
    (within : last ≤ (vista.node vista.bottom).level) :
    (audit? vista leaders candidate last).isSome = true ↔
      Pass leaders candidate last (vista.node vista.bottom).level vista.denotes := by
  constructor
  · intro accepted
    cases result : audit? vista leaders candidate last with
    | none => simp [result] at accepted
    | some witness => exact audit_pass vista leaders candidate last witness result
  · intro passes
    obtain ⟨witness, accepted⟩ := pass_audit vista valid leaders candidate last within passes
    simp [accepted]

end Counting.Executable
