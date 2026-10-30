import DirectedCountingFormalization.CrossExecutionPotential

/-!
# Abstract branching-prefix counting certificate

This file isolates the finite arithmetic at the end of the proposed
branching-prefix argument.  The intended semantic potential is

`surplus + 2 * (candidate - classCount) - deficit`.

Constructing that potential from a concrete history-tree prefix, and proving
that the appropriate kind of transition strictly decreases it, remain
explicit fields of `BranchingPrefixCertificate`.  Once those fields are
available, the contradiction at length `2 * candidate - 2` is completely
kernel checked below.

The abstraction is deliberate: it prevents the graph/view accounting still
under audit from being silently treated as proved arithmetic.
-/

namespace DirectedCounting

/-- The generalized matrix lemma already discharges the minimum-ratio part
of a false nonbranching payment for every target vector different from the
candidate, regardless of its total size. -/
theorem fixedPotential_strict_of_diff
    {q : Nat}
    {M : Nat → Nat → Nat} {d y old target : Nat → Nat}
    {leader : Nat}
    (hyPos : ∀ i, i < q → 0 < y i)
    (hleader : leader < q)
    (hyLeader : y leader = 1)
    (hzLeader : target leader = 1)
    (hDiff : DiffersOn q target y)
    (hMono : ∀ i, i < q → target i ≤ old i)
    (hBalance : BalancedRowSystem q M d y)
    (hCut : HasOutgoingCut q M)
    (hDemand : ∀ i, i < q → old i = target i →
      rowSum q M target i ≤ d i * target i) :
    potential q y old < potential q y target := by
  obtain ⟨i, hMin, hLoss⟩ := minimum_ratio_loss_of_diff
    hyPos hleader hyLeader hzLeader hDiff hMono hBalance hCut hDemand
  exact potential_strict_of_min_loss hMono hMin.1
    (minRatio_le_candidate hMin hleader hyLeader hzLeader) hLoss

/-- The natural-valued form of the proposed cross-partition potential.

When `deficit ≤ candidate - classCount`, this is the same as
`surplus + 2 * (candidate - classCount) - deficit`, but the displayed form
makes the two remaining resource budgets explicit and avoids relying on a
subtraction reassociation law for truncated natural subtraction.
-/
def branchingPrefixPotential
    (candidate classCount deficit surplus : Nat) : Nat :=
  surplus + (candidate - classCount) +
    ((candidate - classCount) - deficit)

/-! ## Fixed-index credit equals the branching-prefix potential -/

def indexedDeficit (q : Nat) (y z : Nat → Nat) : Nat :=
  sumN q (fun i ↦ y i - z i)

def indexedSurplus (q : Nat) (y z : Nat → Nat) : Nat :=
  sumN q (fun i ↦ if y i < z i then 1 else 0)

/-- The recursive arithmetic-kernel sum is the ordinary sum over `Fin q`.
This public adapter keeps the Nat-indexed matrix lemmas and the Fintype
refinement lemmas on one checked interface. -/
theorem sumN_eq_fin_sum (q : Nat) (f : Nat → Nat) :
    sumN q f = ∑ i : Fin q, f i.1 := by
  rw [Fin.sum_univ_eq_sum_range f]
  induction q with
  | zero => simp
  | succ q ih =>
      simp only [sumN_succ, Finset.sum_range_succ, ih]

/-- Reindex the matrix-facing deficit as the refinement module's finite
deficit statistic. -/
theorem indexedDeficit_eq_crossDeficit_fin
    (q : Nat) (y z : Nat → Nat) :
    indexedDeficit q y z =
      crossDeficit (fun i : Fin q ↦ y i.1) (fun i : Fin q ↦ z i.1) := by
  unfold indexedDeficit crossDeficit
  exact sumN_eq_fin_sum q (fun i ↦ y i - z i)

/-- Reindex the matrix-facing surplus count as the refinement module's
finite surplus statistic. -/
theorem indexedSurplus_eq_surplusCount_fin
    (q : Nat) (y z : Nat → Nat) :
    indexedSurplus q y z =
      surplusCount (fun i : Fin q ↦ y i.1) (fun i : Fin q ↦ z i.1) := by
  unfold indexedSurplus surplusCount surplusSet
  rw [sumN_eq_fin_sum]
  simp

/-- Consequently the Nat-indexed branching-prefix potential is literally
the Fintype aggregate credit on `Fin q`. -/
theorem branchingPrefixPotential_eq_crossExecutionCredit_fin
    (candidate q : Nat) (y z : Nat → Nat) :
    branchingPrefixPotential candidate q
        (indexedDeficit q y z) (indexedSurplus q y z) =
      crossExecutionCredit candidate
        (fun i : Fin q ↦ y i.1) (fun i : Fin q ↦ z i.1) := by
  rw [indexedDeficit_eq_crossDeficit_fin,
    indexedSurplus_eq_surplusCount_fin]
  simp [branchingPrefixPotential, crossExecutionCredit]

theorem sumN_add_distrib (q : Nat) (f g : Nat → Nat) :
    sumN q (fun i ↦ f i + g i) = sumN q f + sumN q g := by
  induction q with
  | zero => rfl
  | succ q ih =>
      simp only [sumN_succ, ih]
      omega

theorem sumN_sub_distrib_of_le
    {q : Nat} {f g : Nat → Nat}
    (hLe : ∀ i, i < q → g i ≤ f i) :
    sumN q (fun i ↦ f i - g i) = sumN q f - sumN q g := by
  induction q with
  | zero => rfl
  | succ q ih =>
      simp only [sumN_succ]
      rw [ih (fun i hi ↦ hLe i (by omega))]
      have hPrefix : sumN q g ≤ sumN q f :=
        sumN_mono (fun i hi ↦ hLe i (by omega))
      have hLast := hLe q (by omega)
      omega

theorem sumN_one (q : Nat) : sumN q (fun _ ↦ 1) = q := by
  induction q with
  | zero => rfl
  | succ q ih =>
      simp only [sumN_succ, ih]

/-- Coordinate form of the resource identity. -/
theorem crossFiberCredit_eq_resources
    {reference matching : Nat}
    (hReference : 0 < reference) (hMatching : 0 < matching) :
    crossFiberCredit reference matching =
      (if reference < matching then 1 else 0) +
        ((reference - 1) +
          ((reference - 1) - (reference - matching))) := by
  unfold crossFiberCredit
  by_cases hSurplus : reference < matching
  · simp [hSurplus]
    omega
  · simp [hSurplus]
    omega

/-- For positive fibers of total candidate mass, the matrix module's
fixed-index credit is exactly the aggregate branching-prefix potential. -/
theorem fixedFrontierCredit_eq_branchingPrefixPotential
    {q candidate : Nat} {y z : Nat → Nat}
    (hCandidate : candidate = sumN q y)
    (hyPos : ∀ i, i < q → 0 < y i)
    (hzPos : ∀ i, i < q → 0 < z i) :
    fixedFrontierCredit q y z =
      branchingPrefixPotential candidate q
        (indexedDeficit q y z) (indexedSurplus q y z) := by
  let remaining : Nat → Nat := fun i ↦ y i - 1
  let deficit : Nat → Nat := fun i ↦ y i - z i
  have hDeficitLe : ∀ i, i < q → deficit i ≤ remaining i := by
    intro i hi
    have hy := hyPos i hi
    have hz := hzPos i hi
    simp only [deficit, remaining]
    omega
  have hRemaining : sumN q remaining = sumN q y - q := by
    have hsub := sumN_sub_distrib_of_le
      (q := q) (f := y) (g := fun _ ↦ 1)
      (fun i hi ↦ (hyPos i hi))
    rw [sumN_one] at hsub
    exact hsub
  have hAfterDeficit :
      sumN q (fun i ↦ remaining i - deficit i) =
        sumN q remaining - sumN q deficit :=
    sumN_sub_distrib_of_le hDeficitLe
  calc
    fixedFrontierCredit q y z =
        sumN q (fun i ↦
          (if y i < z i then 1 else 0) +
            (remaining i + (remaining i - deficit i))) := by
      unfold fixedFrontierCredit
      apply sumN_congr
      intro i hi
      exact crossFiberCredit_eq_resources (hyPos i hi) (hzPos i hi)
    _ = indexedSurplus q y z +
        (sumN q remaining +
          sumN q (fun i ↦ remaining i - deficit i)) := by
      rw [sumN_add_distrib]
      rw [sumN_add_distrib]
      rfl
    _ = branchingPrefixPotential candidate q
        (indexedDeficit q y z) (indexedSurplus q y z) := by
      unfold branchingPrefixPotential indexedDeficit indexedSurplus
      simp only [deficit] at hAfterDeficit
      rw [hRemaining, hAfterDeficit, hCandidate]
      omega

/-- A false nonbranching matrix step with nonempty matching fibers strictly
spends the very same branching-prefix potential used by the global trace. -/
theorem branchingPrefixPotential_strict_of_diff
    {q candidate : Nat}
    {M : Nat → Nat → Nat} {d y old target : Nat → Nat}
    {leader : Nat}
    (hCandidate : candidate = sumN q y)
    (hyPos : ∀ i, i < q → 0 < y i)
    (hTargetPos : ∀ i, i < q → 0 < target i)
    (hleader : leader < q)
    (hyLeader : y leader = 1)
    (hzLeader : target leader = 1)
    (hDiff : DiffersOn q target y)
    (hMono : ∀ i, i < q → target i ≤ old i)
    (hBalance : BalancedRowSystem q M d y)
    (hCut : HasOutgoingCut q M)
    (hDemand : ∀ i, i < q → old i = target i →
      rowSum q M target i ≤ d i * target i) :
    branchingPrefixPotential candidate q
        (indexedDeficit q y target) (indexedSurplus q y target) <
      branchingPrefixPotential candidate q
        (indexedDeficit q y old) (indexedSurplus q y old) := by
  have hOldPos : ∀ i, i < q → 0 < old i := by
    intro i hi
    exact Nat.lt_of_lt_of_le (hTargetPos i hi) (hMono i hi)
  rw [← fixedFrontierCredit_eq_branchingPrefixPotential
      hCandidate hyPos hTargetPos,
    ← fixedFrontierCredit_eq_branchingPrefixPotential
      hCandidate hyPos hOldPos]
  exact fixedFrontierCredit_strict_of_diff hyPos hTargetPos hleader
    hyLeader hzLeader hDiff hMono hBalance hCut hDemand

/-- A false nonbranching transition always spends the aggregate
branching-prefix potential, modulo one explicit semantic closure fact.

If the target differs from the candidate vector, the generalized
minimum-ratio cut supplies the loss.  If the two vectors agree, the only
remaining possibility is a coordinate loss: otherwise `hCleanClosure`
identifies the actual order with the candidate, contradicting `hFalse`.

Thus `hCleanClosure` isolates the final equal-target closure premise.  The
matrix-facing balance, cut, and demand hypotheses remain explicit as well. -/
theorem branchingPrefixPotential_strict_of_false_nonbranching
    {q candidate actual : Nat}
    {M : Nat → Nat → Nat} {d y old target : Nat → Nat}
    {leader : Nat}
    (hCandidate : candidate = sumN q y)
    (hyPos : ∀ i, i < q → 0 < y i)
    (hTargetPos : ∀ i, i < q → 0 < target i)
    (hleader : leader < q)
    (hyLeader : y leader = 1)
    (hzLeader : target leader = 1)
    (hMono : ∀ i, i < q → target i ≤ old i)
    (hBalance : BalancedRowSystem q M d y)
    (hCut : HasOutgoingCut q M)
    (hDemand : ∀ i, i < q → old i = target i →
      rowSum q M target i ≤ d i * target i)
    (hFalse : actual ≠ candidate)
    (hCleanClosure :
      (∀ i, i < q → target i = y i) →
      (∀ i, i < q → old i = target i) →
      actual = candidate) :
    branchingPrefixPotential candidate q
        (indexedDeficit q y target) (indexedSurplus q y target) <
      branchingPrefixPotential candidate q
        (indexedDeficit q y old) (indexedSurplus q y old) := by
  by_cases hDiff : DiffersOn q target y
  · exact branchingPrefixPotential_strict_of_diff hCandidate hyPos
      hTargetPos hleader hyLeader hzLeader hDiff hMono hBalance hCut hDemand
  · have hTarget : ∀ i, i < q → target i = y i := by
      intro i hi
      by_contra hNe
      exact hDiff ⟨i, hi, hNe⟩
    have hLoss : ∃ i, i < q ∧ target i < old i := by
      by_contra hNoLoss
      have hClean : ∀ i, i < q → old i = target i := by
        intro i hi
        have hLe := hMono i hi
        have hNotLt : ¬ target i < old i := by
          intro hLt
          exact hNoLoss ⟨i, hi, hLt⟩
        omega
      exact hFalse (hCleanClosure hTarget hClean)
    obtain ⟨i, hi, hLossAt⟩ := hLoss
    have hOldPos : ∀ j, j < q → 0 < old j := by
      intro j hj
      exact Nat.lt_of_lt_of_le (hTargetPos j hj) (hMono j hj)
    rw [← fixedFrontierCredit_eq_branchingPrefixPotential
        hCandidate hyPos hTargetPos,
      ← fixedFrontierCredit_eq_branchingPrefixPotential
        hCandidate hyPos hOldPos]
    exact fixedFrontierCredit_strict_of_equal_target_loss hyPos hTargetPos
      hMono hTarget hi hLossAt

/-- The three integer statistics needed from one selected history frontier.

The inequalities are precisely what positivity of all represented classes
and black-conserved positive candidate weights must supply. -/
structure BranchingPrefixState (candidate : Nat) where
  classCount : Nat
  deficit : Nat
  surplus : Nat
  classCount_le : classCount ≤ candidate
  deficit_le : deficit ≤ candidate - classCount

namespace BranchingPrefixState

/-- Value of the cross-partition potential on one frontier. -/
def value {candidate : Nat} (state : BranchingPrefixState candidate) : Nat :=
  branchingPrefixPotential candidate state.classCount state.deficit
    state.surplus

/-- Credits recording the exact increase in reference classes and deficit
between two consecutive selected frontiers.  The surplus-growth inequality
is the arithmetic conclusion of the fiberwise refinement lemma. -/
structure RefinementCredits {candidate : Nat}
    (old new : BranchingPrefixState candidate) where
  classCredit : Nat
  deficitCredit : Nat
  class_update : new.classCount = old.classCount + classCredit
  deficit_update : new.deficit = old.deficit + deficitCredit
  surplus_growth : new.surplus ≤
    old.surplus + classCredit + deficitCredit

namespace RefinementCredits

/-- A genuine class refinement strictly decreases the potential. -/
theorem value_strict_of_classCredit
    {candidate : Nat} {old new : BranchingPrefixState candidate}
    (credits : RefinementCredits old new)
    (hCredit : 0 < credits.classCredit) :
    new.value < old.value := by
  unfold BranchingPrefixState.value branchingPrefixPotential
  have holdClass := old.classCount_le
  have hnewClass := new.classCount_le
  have holdDeficit := old.deficit_le
  have hnewDeficit := new.deficit_le
  have hclass := credits.class_update
  have hdeficit := credits.deficit_update
  have hsurplus := credits.surplus_growth
  omega

/-- A false nonbranching transition strictly decreases the potential when
it either increases deficit or kills a surplus coordinate. -/
theorem value_strict_of_nonbranching_payment
    {candidate : Nat} {old new : BranchingPrefixState candidate}
    (credits : RefinementCredits old new)
    (hNoClassCredit : credits.classCredit = 0)
    (hSurplusMono : new.surplus ≤ old.surplus)
    (hPayment : 0 < credits.deficitCredit ∨
      new.surplus < old.surplus) :
    new.value < old.value := by
  unfold BranchingPrefixState.value branchingPrefixPotential
  have holdClass := old.classCount_le
  have hnewClass := new.classCount_le
  have holdDeficit := old.deficit_le
  have hnewDeficit := new.deficit_le
  have hclass := credits.class_update
  have hdeficit := credits.deficit_update
  rcases hPayment with hDeficit | hSurplus
  · omega
  · omega

end RefinementCredits

/-- The exact leader/nonleader initial frontier gives the universal initial
potential bound.  The formula for `surplus` expresses that only the ordinary
class is surplus, and exactly when the compatible execution is larger. -/
theorem initial_value_le
    {candidate actual : Nat} (state : BranchingPrefixState candidate)
    (hCandidate : 2 ≤ candidate)
    (hClasses : state.classCount = 2)
    (hDeficit : state.deficit = candidate - actual)
    (hSurplus : state.surplus = if candidate < actual then 1 else 0) :
    state.value ≤ 2 * candidate - 3 := by
  unfold BranchingPrefixState.value branchingPrefixPotential
  by_cases hLarger : candidate < actual
  · rw [hClasses, hDeficit, hSurplus, if_pos hLarger]
    omega
  · rw [hClasses, hDeficit, hSurplus, if_neg hLarger]
    omega

/-! ### Adapter from the fiberwise refinement module -/

variable {Old New : Type*} [Fintype Old] [Fintype New]
  [DecidableEq Old]

/-- Aggregate old-frontier state extracted from concrete refinement fibers. -/
noncomputable def oldStateOfRefinement
    (R : RefinementData Old New) (order : Nat)
    (hOrder : (∑ i, R.yOld i) = order) : BranchingPrefixState order :=
  { classCount := Fintype.card Old
    deficit := crossDeficit R.yOld R.zOld
    surplus := surplusCount R.yOld R.zOld
    classCount_le := (R.refinement_state_bounds order hOrder).1
    deficit_le := (R.refinement_state_bounds order hOrder).2.1 }

/-- Aggregate new-frontier state extracted from concrete refinement fibers. -/
noncomputable def newStateOfRefinement
    (R : RefinementData Old New) (order : Nat)
    (hOrder : (∑ i, R.yOld i) = order) : BranchingPrefixState order :=
  { classCount := Fintype.card New
    deficit := crossDeficit R.yNew R.zNew
    surplus := surplusCount R.yNew R.zNew
    classCount_le := (R.refinement_state_bounds order hOrder).2.2.1
    deficit_le := (R.refinement_state_bounds order hOrder).2.2.2 }

/-- `RefinementData` constructs all arithmetic credits required by the
explicit prefix certificate. -/
noncomputable def creditsOfRefinement
    (R : RefinementData Old New) (order : Nat)
    (hOrder : (∑ i, R.yOld i) = order) :
    RefinementCredits (oldStateOfRefinement R order hOrder)
      (newStateOfRefinement R order hOrder) where
  classCredit := R.classRefinementCredit
  deficitCredit := R.deficitRefinementCredit
  class_update := by
    simpa [oldStateOfRefinement, newStateOfRefinement] using
      R.classCount_update
  deficit_update := by
    simpa [oldStateOfRefinement, newStateOfRefinement] using
      R.crossDeficit_update
  surplus_growth := by
    simpa [oldStateOfRefinement, newStateOfRefinement] using
      R.surplus_growth_by_refinementCredits

/-- The aggregate state value is definitionally the fiberwise
`crossExecutionCredit`. -/
theorem oldState_value_eq_crossExecutionCredit
    (R : RefinementData Old New) (order : Nat)
    (hOrder : (∑ i, R.yOld i) = order) :
    (oldStateOfRefinement R order hOrder).value =
      crossExecutionCredit order R.yOld R.zOld := by
  simp [BranchingPrefixState.value, branchingPrefixPotential,
    crossExecutionCredit, oldStateOfRefinement]

/-- Likewise at the new frontier. -/
theorem newState_value_eq_crossExecutionCredit
    (R : RefinementData Old New) (order : Nat)
    (hOrder : (∑ i, R.yOld i) = order) :
    (newStateOfRefinement R order hOrder).value =
      crossExecutionCredit order R.yNew R.zNew := by
  simp [BranchingPrefixState.value, branchingPrefixPotential,
    crossExecutionCredit, newStateOfRefinement]

/-- A genuine split in `RefinementData` supplies the positive class credit
required by `ExplicitBranchingPrefixCertificate`. -/
theorem creditsOfRefinement_classCredit_pos
    (R : RefinementData Old New) (order : Nat)
    (hOrder : (∑ i, R.yOld i) = order)
    (hBranch : Fintype.card Old < Fintype.card New) :
    0 < (creditsOfRefinement R order hOrder).classCredit := by
  simp only [creditsOfRefinement]
  unfold RefinementData.classRefinementCredit
  omega

/-- The concrete fiberwise class-refinement theorem agrees with the
aggregate-credit descent used by the prefix certificate. -/
theorem value_strict_of_refinementData_branch
    (R : RefinementData Old New) (order : Nat)
    (hOrder : (∑ i, R.yOld i) = order)
    (hBranch : Fintype.card Old < Fintype.card New) :
    (newStateOfRefinement R order hOrder).value <
      (oldStateOfRefinement R order hOrder).value := by
  rw [oldState_value_eq_crossExecutionCredit,
    newState_value_eq_crossExecutionCredit]
  exact R.crossExecutionCredit_strict_of_classRefinement
    order hOrder hBranch

end BranchingPrefixState

/-- In the initial two-class frontier, a larger compatible network has one
surplus coordinate and no deficit, giving exactly `2 * candidate - 3`
units of potential. -/
theorem branchingPrefixPotential_initial_larger
    {candidate : Nat} (hCandidate : 2 ≤ candidate) :
    branchingPrefixPotential candidate 2 0 1 = 2 * candidate - 3 := by
  unfold branchingPrefixPotential
  omega

/-- For a smaller compatible network of order `actual`, the initial
potential is no larger than the larger-network worst case. -/
theorem branchingPrefixPotential_initial_smaller_le
    {candidate actual : Nat}
    (hActual : 2 ≤ actual) (hSmaller : actual < candidate) :
    branchingPrefixPotential candidate 2 (candidate - actual) 0 ≤
      2 * candidate - 3 := by
  unfold branchingPrefixPotential
  omega

/-! ### The initial leader/nonleader profiles -/

/-- The two coordinates of the initial partition: the unique leader and all
ordinary agents.  Only indices below two are used. -/
def initialTwoClassProfile (order i : Nat) : Nat :=
  if i = 0 then 1 else order - 1

theorem initialTwoClassProfile_total {order : Nat} (hOrder : 1 ≤ order) :
    sumN 2 (initialTwoClassProfile order) = order := by
  simp [sumN, initialTwoClassProfile]
  omega

theorem initialTwoClassProfile_pos {order : Nat} (hOrder : 2 ≤ order) :
    ∀ i, i < 2 → 0 < initialTwoClassProfile order i := by
  intro i hi
  have hiCases : i = 0 ∨ i = 1 := by omega
  rcases hiCases with rfl | rfl
  · simp [initialTwoClassProfile]
  · simp [initialTwoClassProfile]
    omega

/-- The initial deficit is exactly the truncated order difference. -/
theorem initialTwoClassProfile_deficit
    {candidate actual : Nat} (_hCandidate : 2 ≤ candidate)
    (hActual : 2 ≤ actual) :
    indexedDeficit 2 (initialTwoClassProfile candidate)
      (initialTwoClassProfile actual) = candidate - actual := by
  simp [indexedDeficit, sumN, initialTwoClassProfile]
  omega

/-- Initially only the ordinary coordinate can be surplus. -/
theorem initialTwoClassProfile_surplus
    {candidate actual : Nat} (_hCandidate : 2 ≤ candidate)
    (_hActual : 2 ≤ actual) :
    indexedSurplus 2 (initialTwoClassProfile candidate)
      (initialTwoClassProfile actual) =
        if candidate < actual then 1 else 0 := by
  by_cases hLarger : candidate < actual
  · simp [indexedSurplus, sumN, initialTwoClassProfile, hLarger]
    omega
  · simp [indexedSurplus, sumN, initialTwoClassProfile, hLarger]
    omega

/-- The concrete two-class profiles attain the universal initial bound. -/
theorem initialTwoClassProfile_potential_le
    {candidate actual : Nat} (hCandidate : 2 ≤ candidate)
    (hActual : 2 ≤ actual) :
    branchingPrefixPotential candidate 2
        (indexedDeficit 2 (initialTwoClassProfile candidate)
          (initialTwoClassProfile actual))
        (indexedSurplus 2 (initialTwoClassProfile candidate)
          (initialTwoClassProfile actual)) ≤
      2 * candidate - 3 := by
  rw [initialTwoClassProfile_deficit hCandidate hActual,
    initialTwoClassProfile_surplus hCandidate hActual]
  unfold branchingPrefixPotential
  split <;> omega

/-- An abstract finite trace whose natural-valued measure drops at every
transition. -/
structure DescendingPrefixTrace (R : Nat) where
  value : Nat → Nat
  step : ∀ h, h < R → value (h + 1) < value h

namespace DescendingPrefixTrace

/-- A strictly descending natural-valued trace cannot contain more
transitions than its initial value. -/
theorem length_le_initial {R : Nat} (trace : DescendingPrefixTrace R) :
    R ≤ trace.value 0 := by
  have hdescent : trace.value R + R ≤ trace.value 0 := by
    have hraw := descent_add_le_after_dirty_steps
      trace.value (fun _ ↦ False) 0 R
      (by
        intro _ _ hfalse
        exact hfalse)
      (by
        intro t ht
        simpa using trace.step t ht)
    simpa using hraw
  omega

/-- If the initial value is bounded by `B`, the trace length is bounded by
the same `B`. -/
theorem length_le_bound {R B : Nat} (trace : DescendingPrefixTrace R)
    (hInitial : trace.value 0 ≤ B) : R ≤ B := by
  exact Nat.le_trans trace.length_le_initial hInitial

end DescendingPrefixTrace

/--
The proof-relevant interface expected from a locally recognized branching
prefix.

`branching` classifies selected-prefix transitions.  The two descent fields
are intentionally separate because their semantic proofs use different
facts:

* branching descent uses black conservation and the refinement inequality;
* false nonbranching descent uses balance, support strong connectivity,
  minimum-ratio loss, and clean-transition closure.

No field assumes the desired conclusion `actual = candidate`.
-/
structure BranchingPrefixCertificate
    (candidate actual R : Nat) where
  two_le_candidate : 2 ≤ candidate
  potential : Nat → Nat
  branching : Nat → Prop
  initial_bound : potential 0 ≤ 2 * candidate - 3
  branching_descent : ∀ h, h < R → branching h →
    potential (h + 1) < potential h
  false_nonbranching_descent : actual ≠ candidate →
    ∀ h, h < R → ¬ branching h →
      potential (h + 1) < potential h
  certificate_length : 2 * candidate - 2 ≤ R

namespace BranchingPrefixCertificate

/-- If the candidate is false, every transition of the selected prefix
strictly decreases its potential. -/
def descendingTrace
    {candidate actual R : Nat}
    (certificate : BranchingPrefixCertificate candidate actual R)
    (hFalse : actual ≠ candidate) : DescendingPrefixTrace R where
  value := certificate.potential
  step := by
    intro h hh
    by_cases hBranch : certificate.branching h
    · exact certificate.branching_descent h hh hBranch
    · exact certificate.false_nonbranching_descent hFalse h hh hBranch

/-- Arithmetic soundness of a `2 * candidate - 2` branching-prefix
certificate. -/
theorem sound
    {candidate actual R : Nat}
    (certificate : BranchingPrefixCertificate candidate actual R) :
    actual = candidate := by
  by_cases hEqual : actual = candidate
  · exact hEqual
  · exfalso
    let hTrace : DescendingPrefixTrace R := certificate.descendingTrace hEqual
    have hInitial : hTrace.value 0 ≤ 2 * candidate - 3 := by
      simpa [hTrace, descendingTrace] using certificate.initial_bound
    have hUpper : R ≤ 2 * candidate - 3 :=
      hTrace.length_le_bound hInitial
    have hLower := certificate.certificate_length
    have hCandidate := certificate.two_le_candidate
    omega

end BranchingPrefixCertificate

/-!
## Semantic-facing credit trace

The next structure eliminates the arbitrary potential and arbitrary descent
fields from `BranchingPrefixCertificate`.  It stores only the explicit
frontier statistics, refinement credits, and the two payments which the
history/matrix layer must prove.  The arithmetic lemmas above derive every
strict potential step.
-/

structure ExplicitBranchingPrefixCertificate
    (candidate actual R : Nat) where
  two_le_candidate : 2 ≤ candidate
  state : Nat → BranchingPrefixState candidate
  branching : Nat → Prop
  credits : ∀ h, h < R →
    BranchingPrefixState.RefinementCredits (state h) (state (h + 1))

  initial_classes : (state 0).classCount = 2
  initial_deficit : (state 0).deficit = candidate - actual
  initial_surplus : (state 0).surplus =
    if candidate < actual then 1 else 0

  branching_credit : ∀ h (hh : h < R), branching h →
    0 < (credits h hh).classCredit
  nonbranching_class_credit : ∀ h (hh : h < R), ¬ branching h →
    (credits h hh).classCredit = 0
  nonbranching_surplus_mono : ∀ h, h < R → ¬ branching h →
    (state (h + 1)).surplus ≤ (state h).surplus
  false_nonbranching_payment : actual ≠ candidate →
    ∀ h (hh : h < R), ¬ branching h →
      0 < (credits h hh).deficitCredit ∨
        (state (h + 1)).surplus < (state h).surplus

  certificate_length : 2 * candidate - 2 ≤ R

namespace ExplicitBranchingPrefixCertificate

/-- The explicit state/credit interface constructs the smaller abstract
certificate; in particular, neither its potential nor its descent is an
independent assumption. -/
def toAbstract
    {candidate actual R : Nat}
    (certificate : ExplicitBranchingPrefixCertificate candidate actual R) :
    BranchingPrefixCertificate candidate actual R where
  two_le_candidate := certificate.two_le_candidate
  potential := fun h ↦ (certificate.state h).value
  branching := certificate.branching
  initial_bound :=
    BranchingPrefixState.initial_value_le (certificate.state 0)
      certificate.two_le_candidate certificate.initial_classes
      certificate.initial_deficit certificate.initial_surplus
  branching_descent := by
    intro h hh hBranch
    exact (certificate.credits h hh).value_strict_of_classCredit
      (certificate.branching_credit h hh hBranch)
  false_nonbranching_descent := by
    intro hFalse h hh hNonbranch
    exact (certificate.credits h hh).value_strict_of_nonbranching_payment
      (certificate.nonbranching_class_credit h hh hNonbranch)
      (certificate.nonbranching_surplus_mono h hh hNonbranch)
      (certificate.false_nonbranching_payment hFalse h hh hNonbranch)
  certificate_length := certificate.certificate_length

/-- Kernel-checked soundness from the explicit frontier statistics and
transition credits. -/
theorem sound
    {candidate actual R : Nat}
    (certificate : ExplicitBranchingPrefixCertificate candidate actual R) :
    actual = candidate :=
  certificate.toAbstract.sound

end ExplicitBranchingPrefixCertificate

/-!
## Semantic audit boundary

The theorem above verifies the final potential/length argument, but a local
history-tree predicate must still establish all of the following before it
can construct `BranchingPrefixCertificate`:

1. selected nodes begin with the complete leader/nonleader frontier;
2. positive integral candidate weights black-conserve, so their total is
   fixed and their class count never exceeds the candidate;
3. actual selected classes are whole global history classes, and selected
   child classes are disjoint subsets of their selected parent class;
4. the deficit/surplus refinement inequality proves strict potential descent
   at every selected branching transition;
5. every selected nonbranching transition has a balanced, strongly connected
   source-row matrix with the correct late-degree demand inequality;
6. connect each concrete nonbranching window to the matrix hypotheses above;
   the generalized unequal-target descent, its conversion to the aggregate
   potential, and the `Nat`/`Fin q` reindexing are all checked in this file;
7. prove the remaining `hCleanClosure` implication: when the target equals
   the candidate vector and no coordinate peels, saturation and round-graph
   strong connectivity force the actual order to equal the candidate.

Those items are semantic proof obligations, not axioms hidden by this file.
-/

end DirectedCounting
