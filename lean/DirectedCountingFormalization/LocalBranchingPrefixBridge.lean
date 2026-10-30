import DirectedCountingFormalization.BranchingPrefixCertificate

/-!
# Frontier data to the explicit branching-prefix certificate

This file records the smallest intermediate interface between a finite local
history-view checker and `ExplicitBranchingPrefixCertificate`.

The reference weights `y` and their black-parent conservation are intended to
be extracted and checked locally.  The matching weights `z` are ghost data:
in the semantic proof they count agents of an arbitrary compatible execution
whose histories match the selected visible nodes.  Positivity and
subconservation of `z` are therefore semantic realization theorems, not work
performed by the executable checker.

The only transition fact not implied by refinement bookkeeping is
`false_nonbranching_descent`.  A concrete view/matrix layer must prove it from
the locally checked balance/support conditions and the actual round graph.
Once that theorem is supplied, the construction of the explicit certificate
below is automatic.

The functions are indexed by `Nat` to match the existing certificate API.
Only levels `0, ..., R` are consumed.  A finite checker can extend its final
stored frontier constantly after `R` before using this adapter.
-/

set_option warningAsError true

namespace DirectedCounting

open scoped BigOperators

/-- Locally checkable data common to all executions compatible with a
selected branching prefix. -/
structure LocalBranchingPrefixData (candidate R : Nat) where
  two_le_candidate : 2 ≤ candidate
  classCount : Nat → Nat
  weight : (h : Nat) → Fin (classCount h) → Nat
  parent : (h : Nat) → Fin (classCount (h + 1)) → Fin (classCount h)

  weight_pos : ∀ h, h ≤ R → ∀ i, 0 < weight h i
  weight_total : ∀ h, h ≤ R → (∑ i, weight h i) = candidate
  weight_conserve : ∀ h, h < R → ∀ i,
    fiberMass (parent h) (weight (h + 1)) i = weight h i

  initial_classes : classCount 0 = 2
  certificate_length : 2 * candidate - 2 ≤ R

namespace LocalBranchingPrefixData

/-- Positive exact black conservation already implies the black-coverage
condition that an executable recognizer will normally check directly. -/
theorem parent_surjective
    {candidate R : Nat} (data : LocalBranchingPrefixData candidate R)
    (h : Nat) (hh : h < R) : Function.Surjective (data.parent h) := by
  intro i
  by_contra hnone
  push Not at hnone
  have hfiber : refinementFiber (data.parent h) i = ∅ := by
    ext j
    simp [refinementFiber, hnone j]
  have hconserve := data.weight_conserve h hh i
  rw [fiberMass, hfiber] at hconserve
  simp only [Finset.sum_empty] at hconserve
  have hpos := data.weight_pos h (Nat.le_of_lt hh) i
  omega

/-- Hence a transition with no class-count increase has a bijective black
parent map, providing the alignment used by the square matrix step. -/
theorem parent_bijective_of_nonbranch
    {candidate R : Nat} (data : LocalBranchingPrefixData candidate R)
    (h : Nat) (hh : h < R)
    (hnonbranch : ¬ data.classCount h < data.classCount (h + 1)) :
    Function.Bijective (data.parent h) := by
  have hsurjective := data.parent_surjective h hh
  have hcardLe := Fintype.card_le_of_surjective (data.parent h) hsurjective
  have hcardEq :
      Fintype.card (Fin (data.classCount (h + 1))) =
        Fintype.card (Fin (data.classCount h)) := by
    simp only [Fintype.card_fin] at hcardLe ⊢
    omega
  exact (Fintype.bijective_iff_surjective_and_card (data.parent h)).2
    ⟨hsurjective, hcardEq⟩

/-- Canonical child-to-parent alignment at a nonbranching transition. -/
noncomputable def parentEquivOfNonbranch
    {candidate R : Nat} (data : LocalBranchingPrefixData candidate R)
    (h : Nat) (hh : h < R)
    (hnonbranch : ¬ data.classCount h < data.classCount (h + 1)) :
    Fin (data.classCount (h + 1)) ≃ Fin (data.classCount h) :=
  Equiv.ofBijective (data.parent h)
    (data.parent_bijective_of_nonbranch h hh hnonbranch)

/-- On a nonbranching transition the unique child of an old class carries
exactly the same candidate mass. -/
theorem weight_child_eq_of_nonbranch
    {candidate R : Nat} (data : LocalBranchingPrefixData candidate R)
    (h : Nat) (hh : h < R)
    (hnonbranch : ¬ data.classCount h < data.classCount (h + 1))
    (i : Fin (data.classCount h)) :
    data.weight (h + 1)
        ((data.parentEquivOfNonbranch h hh hnonbranch).symm i) =
      data.weight h i := by
  classical
  let e := data.parentEquivOfNonbranch h hh hnonbranch
  let child := e.symm i
  have hparentChild : data.parent h child = i := by
    exact e.apply_symm_apply i
  have hfiber : refinementFiber (data.parent h) i = {child} := by
    ext j
    simp only [refinementFiber, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    constructor
    · intro hj
      apply e.injective
      change data.parent h j = data.parent h child
      rw [hj, hparentChild]
    · rintro rfl
      exact hparentChild
  have hconserve := data.weight_conserve h hh i
  rw [fiberMass, hfiber] at hconserve
  simpa [e, child] using hconserve

end LocalBranchingPrefixData

/-- Semantic realization of the locally selected frontiers inside one
compatible execution of order `actual`. -/
structure LocalBranchingPrefixData.Realization
    {candidate R : Nat} (data : LocalBranchingPrefixData candidate R)
    (actual : Nat) where
  matching : (h : Nat) → Fin (data.classCount h) → Nat
  matching_pos : ∀ h, h ≤ R → ∀ i, 0 < matching h i
  matching_subconserve : ∀ h, h < R → ∀ i,
    fiberMass (data.parent h) (matching (h + 1)) i ≤ matching h i

  initial_deficit :
    crossDeficit (data.weight 0) (matching 0) = candidate - actual
  initial_surplus :
    surplusCount (data.weight 0) (matching 0) =
      if candidate < actual then 1 else 0

  /-- One-step descent hypothesis for a false, nonbranching candidate.
  Refinement bookkeeping converts this local matrix condition into the
  disjunctive payment required by the explicit prefix certificate below.
  The strict inequality is part of this structure's supplied data. -/
  false_nonbranching_descent : actual ≠ candidate →
    ∀ h, h < R →
      ¬ data.classCount h < data.classCount (h + 1) →
      crossExecutionCredit candidate
          (data.weight (h + 1)) (matching (h + 1)) <
        crossExecutionCredit candidate (data.weight h) (matching h)

namespace LocalBranchingPrefixData.Realization

variable {candidate actual R : Nat}
variable {data : LocalBranchingPrefixData candidate R}

/-- One selected adjacent pair is concrete `RefinementData`. -/
noncomputable def refinement
    (realization : data.Realization actual) (h : Nat) (hh : h < R) :
    RefinementData (Fin (data.classCount h))
      (Fin (data.classCount (h + 1))) where
  parent := data.parent h
  yOld := data.weight h
  zOld := realization.matching h
  yNew := data.weight (h + 1)
  zNew := realization.matching (h + 1)
  yOld_pos := data.weight_pos h (Nat.le_of_lt hh)
  zOld_pos := realization.matching_pos h (Nat.le_of_lt hh)
  yNew_pos := data.weight_pos (h + 1) (Nat.succ_le_iff.mpr hh)
  zNew_pos := realization.matching_pos (h + 1) (Nat.succ_le_iff.mpr hh)
  y_conserve := data.weight_conserve h hh
  z_subconserve := realization.matching_subconserve h hh

/-- The aggregate state at a selected frontier. -/
noncomputable def frontierState
    (realization : data.Realization actual) (h : Nat) :
    BranchingPrefixState candidate := by
  by_cases hh : h ≤ R
  · exact
      { classCount := data.classCount h
        deficit := crossDeficit (data.weight h) (realization.matching h)
        surplus := surplusCount (data.weight h) (realization.matching h)
        classCount_le := by
          have hcard := card_le_sum_of_pos (data.weight h)
            (data.weight_pos h hh)
          simpa [data.weight_total h hh] using hcard
        deficit_le := by
          have hdeficit := crossDeficit_le_sum_sub_card_of_pos
            (data.weight h) (realization.matching h)
            (data.weight_pos h hh) (realization.matching_pos h hh)
          simpa [data.weight_total h hh] using hdeficit }
  · exact
      { classCount := 1
        deficit := 0
        surplus := 0
        classCount_le := by
          have hcandidate := data.two_le_candidate
          omega
        deficit_le := Nat.zero_le _ }

/-- Refinement arithmetic constructs the exact credits between consecutive
aggregate states. -/
noncomputable def frontierCredits
    (realization : data.Realization actual) (h : Nat) (hh : h < R) :
    BranchingPrefixState.RefinementCredits
      (realization.frontierState h)
      (realization.frontierState (h + 1)) := by
  let step := realization.refinement h hh
  exact
    { classCredit := step.classRefinementCredit
      deficitCredit := step.deficitRefinementCredit
      class_update := by
        simpa [frontierState, Nat.le_of_lt hh, Nat.succ_le_iff.mpr hh,
          step, refinement] using step.classCount_update
      deficit_update := by
        simpa [frontierState, Nat.le_of_lt hh, Nat.succ_le_iff.mpr hh,
          step, refinement] using step.crossDeficit_update
      surplus_growth := by
        simpa [frontierState, Nat.le_of_lt hh, Nat.succ_le_iff.mpr hh,
          step, refinement] using
          step.surplus_growth_by_refinementCredits }

theorem classCredit_pos_of_branch
    (realization : data.Realization actual) (h : Nat) (hh : h < R)
    (hbranch : data.classCount h < data.classCount (h + 1)) :
    0 < (realization.frontierCredits h hh).classCredit := by
  change 0 < Fintype.card (Fin (data.classCount (h + 1))) -
    Fintype.card (Fin (data.classCount h))
  simp only [Fintype.card_fin]
  omega

theorem classCredit_eq_zero_of_nonbranch
    (realization : data.Realization actual) (h : Nat) (hh : h < R)
    (hnonbranch : ¬ data.classCount h < data.classCount (h + 1)) :
    (realization.frontierCredits h hh).classCredit = 0 := by
  have hmono := (realization.refinement h hh).classCount_mono
  change Fintype.card (Fin (data.classCount (h + 1))) -
    Fintype.card (Fin (data.classCount h)) = 0
  simp only [Fintype.card_fin] at hmono ⊢
  omega

theorem surplus_mono_of_nonbranch
    (realization : data.Realization actual) (h : Nat) (hh : h < R)
    (hnonbranch : ¬ data.classCount h < data.classCount (h + 1)) :
    (realization.frontierState (h + 1)).surplus ≤
      (realization.frontierState h).surplus := by
  have hclasses := (realization.refinement h hh).classCount_mono
  have hsurplus :
      surplusCount (data.weight (h + 1)) (realization.matching (h + 1)) +
          data.classCount h ≤
        surplusCount (data.weight h) (realization.matching h) +
          data.classCount (h + 1) := by
    simpa [refinement] using
      (realization.refinement h hh).surplus_refinement_inequality
  simp only [Fintype.card_fin] at hclasses
  simp only [frontierState, Nat.le_of_lt hh, Nat.succ_le_iff.mpr hh,
    ↓reduceDIte]
  omega

/-- At equal class count, strict descent of the native credit must be paid
by one of the two remaining monotone statistics. -/
theorem payment_of_credit_strict_of_nonbranch
    (realization : data.Realization actual) (h : Nat) (hh : h < R)
    (hnonbranch : ¬ data.classCount h < data.classCount (h + 1))
    (hstrict :
      crossExecutionCredit candidate
          (data.weight (h + 1)) (realization.matching (h + 1)) <
        crossExecutionCredit candidate
          (data.weight h) (realization.matching h)) :
    crossDeficit (data.weight h) (realization.matching h) <
        crossDeficit (data.weight (h + 1))
          (realization.matching (h + 1)) ∨
      surplusCount (data.weight (h + 1))
          (realization.matching (h + 1)) <
        surplusCount (data.weight h) (realization.matching h) := by
  have hclasses := (realization.refinement h hh).classCount_mono
  simp only [Fintype.card_fin] at hclasses
  have hclassEq : data.classCount (h + 1) = data.classCount h := by
    omega
  have hdeficitMono := (realization.refinement h hh).crossDeficit_mono
  have hsurplusMono := realization.surplus_mono_of_nonbranch h hh hnonbranch
  simp only [frontierState, Nat.le_of_lt hh, Nat.succ_le_iff.mpr hh,
    ↓reduceDIte] at hsurplusMono
  by_cases hdeficit :
      crossDeficit (data.weight h) (realization.matching h) <
        crossDeficit (data.weight (h + 1))
          (realization.matching (h + 1))
  · exact Or.inl hdeficit
  · right
    by_contra hsurplus
    have hdeficitEq :
        crossDeficit (data.weight h) (realization.matching h) =
          crossDeficit (data.weight (h + 1))
            (realization.matching (h + 1)) := by
      simpa [refinement] using Nat.le_antisymm
        hdeficitMono (Nat.le_of_not_gt hdeficit)
    have hsurplusEq :
        surplusCount (data.weight (h + 1))
            (realization.matching (h + 1)) =
          surplusCount (data.weight h) (realization.matching h) := by
      exact Nat.le_antisymm hsurplusMono (Nat.le_of_not_gt hsurplus)
    unfold crossExecutionCredit at hstrict
    simp only [Fintype.card_fin, hclassEq, hdeficitEq, hsurplusEq] at hstrict
    omega

/-- The finite frontier/refinement data and its semantic realization build
the proof-relevant certificate consumed by the arithmetic soundness theorem. -/
noncomputable def toExplicitCertificate
    (realization : data.Realization actual) :
    ExplicitBranchingPrefixCertificate candidate actual R where
  two_le_candidate := data.two_le_candidate
  state := realization.frontierState
  branching := fun h ↦ data.classCount h < data.classCount (h + 1)
  credits := fun h hh ↦ realization.frontierCredits h hh

  initial_classes := by
    simpa [frontierState] using data.initial_classes
  initial_deficit := by
    simpa [frontierState] using realization.initial_deficit
  initial_surplus := by
    simpa [frontierState] using realization.initial_surplus

  branching_credit := by
    intro h hh hbranch
    exact realization.classCredit_pos_of_branch h hh hbranch
  nonbranching_class_credit := by
    intro h hh hnonbranch
    exact realization.classCredit_eq_zero_of_nonbranch h hh hnonbranch
  nonbranching_surplus_mono := by
    intro h hh hnonbranch
    exact realization.surplus_mono_of_nonbranch h hh hnonbranch
  false_nonbranching_payment := by
    intro hfalse h _hh hnonbranch
    have hstrict := realization.false_nonbranching_descent
      hfalse h _hh hnonbranch
    rcases realization.payment_of_credit_strict_of_nonbranch
        h _hh hnonbranch hstrict with
      hdeficit | hsurplus
    · left
      change 0 < crossDeficit (data.weight (h + 1))
          (realization.matching (h + 1)) -
        crossDeficit (data.weight h) (realization.matching h)
      omega
    · right
      simpa [frontierState, Nat.le_of_lt _hh, Nat.succ_le_iff.mpr _hh]
        using hsurplus

  certificate_length := data.certificate_length

/-- Soundness after the local-code and semantic-realization layers have
discharged their respective obligations. -/
theorem sound (realization : data.Realization actual) :
    actual = candidate :=
  realization.toExplicitCertificate.sound

end LocalBranchingPrefixData.Realization

end DirectedCounting
