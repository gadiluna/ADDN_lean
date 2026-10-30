import DirectedCountingFormalization.CrossExecutionMatrix
import Mathlib.Tactic

/-!
# Potentials across refinements of two executions

This file isolates the combinatorial bookkeeping used when a smaller
execution is compared with a larger execution having the same finite
history.  An old history class may refine into several new classes.  The
smaller execution conserves its agents exactly, while the matching agents of
the larger execution may leave the common histories but can never enter them.

No graph, matrix, or indistinguishability claim is assumed here.  Those
semantic facts are intended to construct `RefinementData`; the results below
then provide the purely finite arithmetic consequences.
-/

namespace DirectedCounting

open scoped BigOperators

/-- Total matching mass on a finite family of history classes. -/
def matchingMass {ι : Type*} [Fintype ι] (z : ι → ℕ) : ℕ :=
  ∑ i, z i

/-- Integral deficit of the matching fiber relative to the reference fiber. -/
def crossDeficit {ι : Type*} [Fintype ι] (y z : ι → ℕ) : ℕ :=
  ∑ i, (y i - z i)

/-- The history classes carrying strictly more matching than reference mass. -/
def surplusSet {ι : Type*} [Fintype ι] (y z : ι → ℕ) : Finset ι :=
  Finset.univ.filter fun i ↦ y i < z i

/-- Number of positive-surplus history classes. -/
def surplusCount {ι : Type*} [Fintype ι] (y z : ι → ℕ) : ℕ :=
  (surplusSet y z).card

/-- The natural-valued cross-execution credit carried by one frontier.

Writing `q` for the number of represented classes, `Δ` for `crossDeficit`,
and `P` for `surplusCount`, this is

`P + (order - q) + ((order - q) - Δ)`.

The two occurrences of `order - q` pay respectively for the possible growth
of `P` under refinement and for strict growth of either `q` or `Δ`.
-/
def crossExecutionCredit {ι : Type*} [Fintype ι]
    (order : ℕ) (y z : ι → ℕ) : ℕ :=
  surplusCount y z + (order - Fintype.card ι) +
    ((order - Fintype.card ι) - crossDeficit y z)

/-- Positivity of every coordinate bounds the number of coordinates by the
total mass. -/
theorem card_le_sum_of_pos {ι : Type*} [Fintype ι]
    (f : ι → ℕ) (hf : ∀ i, 0 < f i) :
    Fintype.card ι ≤ ∑ i, f i := by
  calc
    Fintype.card ι = ∑ _i : ι, 1 := by simp
    _ ≤ ∑ i, f i :=
      Finset.sum_le_sum fun i _ ↦ Nat.succ_le_iff.mpr (hf i)

/-- If both fibers are positive, their integral deficit fits into the
reference mass left after reserving one agent for every class. -/
theorem crossDeficit_le_sum_sub_card_of_pos
    {ι : Type*} [Fintype ι] (y z : ι → ℕ)
    (hyPos : ∀ i, 0 < y i) (hzPos : ∀ i, 0 < z i) :
    crossDeficit y z ≤ (∑ i, y i) - Fintype.card ι := by
  have hpoint : ∀ i : ι, y i - z i ≤ y i - 1 := by
    intro i
    have := hzPos i
    omega
  rw [crossDeficit]
  calc
    (∑ i, (y i - z i)) ≤ ∑ i, (y i - 1) :=
      Finset.sum_le_sum fun i _ ↦ hpoint i
    _ = (∑ i, y i) - ∑ _i : ι, 1 := by
      apply Finset.sum_tsub_distrib
      intro i _
      exact hyPos i
    _ = (∑ i, y i) - Fintype.card ι := by simp

/-- Matching children of one old history class. -/
def refinementFiber {Old New : Type*} [Fintype New] [DecidableEq Old]
    (parent : New → Old) (i : Old) : Finset New :=
  Finset.univ.filter fun j ↦ parent j = i

/-- Sum of a quantity over the children of one old history class. -/
def fiberMass {Old New : Type*} [Fintype New] [DecidableEq Old]
    (parent : New → Old) (f : New → ℕ) (i : Old) : ℕ :=
  ∑ j ∈ refinementFiber parent i, f j

/--
One refinement step shared by a reference execution and a matching
execution.  `y` is exactly conserved in every parent class.  Matching mass
`z` is only subconserved: agents may acquire a history absent from the
reference execution, but histories never merge back into a matching fiber.
-/
structure RefinementData (Old New : Type*) [Fintype Old] [Fintype New]
    [DecidableEq Old] where
  parent : New → Old
  yOld : Old → ℕ
  zOld : Old → ℕ
  yNew : New → ℕ
  zNew : New → ℕ
  yOld_pos : ∀ i, 0 < yOld i
  zOld_pos : ∀ i, 0 < zOld i
  yNew_pos : ∀ j, 0 < yNew j
  zNew_pos : ∀ j, 0 < zNew j
  y_conserve : ∀ i, fiberMass parent yNew i = yOld i
  z_subconserve : ∀ i, fiberMass parent zNew i ≤ zOld i

namespace RefinementData

variable {Old New : Type*} [Fintype Old] [Fintype New]
  [DecidableEq Old]

@[simp] theorem mem_refinementFiber (R : RefinementData Old New) (i : Old)
    (j : New) :
    j ∈ refinementFiber R.parent i ↔ R.parent j = i := by
  simp [refinementFiber]

/-- Fiberwise summation over all old classes counts every new class once. -/
theorem sum_fiberMass (R : RefinementData Old New) (f : New → ℕ) :
    (∑ i, fiberMass R.parent f i) = ∑ j, f j := by
  classical
  simpa [fiberMass, refinementFiber] using
    (Finset.sum_fiberwise_of_maps_to
      (s := (Finset.univ : Finset New))
      (t := (Finset.univ : Finset Old))
      (g := R.parent)
      (fun _ _ ↦ Finset.mem_univ _) f)

/-- Reference mass is conserved globally by a refinement. -/
theorem referenceMass_eq (R : RefinementData Old New) :
    (∑ j, R.yNew j) = ∑ i, R.yOld i := by
  rw [← R.sum_fiberMass R.yNew]
  exact Finset.sum_congr rfl fun i _ ↦ R.y_conserve i

/-- Matching mass cannot increase when histories refine. -/
theorem matchingMass_mono (R : RefinementData Old New) :
    matchingMass R.zNew ≤ matchingMass R.zOld := by
  rw [matchingMass, matchingMass, ← R.sum_fiberMass R.zNew]
  exact Finset.sum_le_sum fun i _ ↦ R.z_subconserve i

theorem crossDeficit_nonneg (R : RefinementData Old New) :
    0 ≤ crossDeficit R.yOld R.zOld := Nat.zero_le _

/-- Each reference deficit is covered by the deficits of its children. -/
theorem parent_deficit_le_children (R : RefinementData Old New) (i : Old) :
    R.yOld i - R.zOld i ≤
      ∑ j ∈ refinementFiber R.parent i, (R.yNew j - R.zNew j) := by
  let F := refinementFiber R.parent i
  have hpoint : ∀ j ∈ F, R.yNew j ≤ R.zNew j + (R.yNew j - R.zNew j) := by
    intro j _
    omega
  have hsum := Finset.sum_le_sum hpoint
  rw [Finset.sum_add_distrib] at hsum
  have hy := R.y_conserve i
  have hz := R.z_subconserve i
  change (∑ j ∈ F, R.yNew j) = R.yOld i at hy
  change (∑ j ∈ F, R.zNew j) ≤ R.zOld i at hz
  apply Nat.sub_le_iff_le_add.mpr
  calc
    R.yOld i = ∑ j ∈ F, R.yNew j := hy.symm
    _ ≤ (∑ j ∈ F, R.zNew j) +
        (∑ j ∈ F, (R.yNew j - R.zNew j)) := hsum
    _ ≤ R.zOld i + (∑ j ∈ F, (R.yNew j - R.zNew j)) :=
      Nat.add_le_add_right hz _
    _ = (∑ j ∈ F, (R.yNew j - R.zNew j)) + R.zOld i := by omega

/-- The integral deficit cannot decrease when common histories refine. -/
theorem crossDeficit_mono (R : RefinementData Old New) :
    crossDeficit R.yOld R.zOld ≤ crossDeficit R.yNew R.zNew := by
  rw [crossDeficit, crossDeficit, ← R.sum_fiberMass
    (fun j ↦ R.yNew j - R.zNew j)]
  exact Finset.sum_le_sum fun i _ ↦ R.parent_deficit_le_children i

/-- Positive matching fibers bound the deficit by reference mass minus classes. -/
theorem crossDeficit_le_reference_sub_card (R : RefinementData Old New)
    (hyPos : ∀ i, 0 < R.yOld i)
    (hzPos : ∀ i, 0 < R.zOld i) :
    crossDeficit R.yOld R.zOld ≤ (∑ i, R.yOld i) - Fintype.card Old := by
  exact crossDeficit_le_sum_sub_card_of_pos R.yOld R.zOld hyPos hzPos

omit [DecidableEq Old] in
/-- Surplus classes form a subset of all classes. -/
theorem surplusCount_le_card (y z : Old → ℕ) :
    surplusCount y z ≤ Fintype.card Old := by
  unfold surplusCount
  calc
    (surplusSet y z).card ≤ (Finset.univ : Finset Old).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ = Fintype.card Old := Finset.card_univ

/-- A nonsurplus parent has at least one nonsurplus matching child. -/
theorem exists_nonsurplus_child (R : RefinementData Old New) (i : Old)
    (hi : ¬ R.yOld i < R.zOld i) :
    ∃ j : New, R.parent j = i ∧ ¬ R.yNew j < R.zNew j := by
  classical
  let F := refinementFiber R.parent i
  have hy := R.y_conserve i
  have hz := R.z_subconserve i
  change (∑ j ∈ F, R.yNew j) = R.yOld i at hy
  change (∑ j ∈ F, R.zNew j) ≤ R.zOld i at hz
  have hF : F.Nonempty := by
    by_contra hempty
    have hzero : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hempty
    rw [hzero] at hy
    simp only [Finset.sum_empty] at hy
    have hp := R.yOld_pos i
    omega
  by_contra hnone
  push Not at hnone
  have hstrict : ∀ j ∈ F, R.yNew j < R.zNew j := by
    intro j hj
    exact hnone j (R.mem_refinementFiber i j |>.mp hj)
  obtain ⟨j, hj⟩ := hF
  have hsumlt :
      (∑ k ∈ F, R.yNew k) < ∑ k ∈ F, R.zNew k :=
    Finset.sum_lt_sum
      (fun k hk ↦ Nat.le_of_lt (hstrict k hk))
      ⟨j, hj, hstrict j hj⟩
  omega

/-- Nonsurplus classes inject through a refinement. -/
theorem nonsurplus_card_mono (R : RefinementData Old New) :
    Fintype.card {i : Old // ¬ R.yOld i < R.zOld i} ≤
      Fintype.card {j : New // ¬ R.yNew j < R.zNew j} := by
  classical
  let child : {i : Old // ¬ R.yOld i < R.zOld i} → New :=
    fun i ↦ Classical.choose (R.exists_nonsurplus_child i i.property)
  have hchild_parent : ∀ i, R.parent (child i) = i.1 := by
    intro i
    exact (Classical.choose_spec
      (R.exists_nonsurplus_child i i.property)).1
  have hchild_nonsurplus : ∀ i, ¬ R.yNew (child i) < R.zNew (child i) := by
    intro i
    exact (Classical.choose_spec
      (R.exists_nonsurplus_child i i.property)).2
  let lift : {i : Old // ¬ R.yOld i < R.zOld i} →
      {j : New // ¬ R.yNew j < R.zNew j} :=
    fun i ↦ ⟨child i, hchild_nonsurplus i⟩
  apply Fintype.card_le_of_injective lift
  intro i k hik
  apply Subtype.ext
  have hvals : child i = child k := congrArg Subtype.val hik
  have hp := congrArg R.parent hvals
  simpa [hchild_parent] using hp

/--
Refinement can create at most one new surplus episode per new reference
class.  Equivalently, `surplusCount - classCount` never increases.
-/
theorem surplus_refinement_inequality (R : RefinementData Old New) :
    surplusCount R.yNew R.zNew + Fintype.card Old ≤
      surplusCount R.yOld R.zOld + Fintype.card New := by
  classical
  have hns := R.nonsurplus_card_mono
  have holdPart :
      Fintype.card {i : Old // ¬ R.yOld i < R.zOld i} +
          surplusCount R.yOld R.zOld = Fintype.card Old := by
    have hc := Fintype.card_subtype_compl
      (p := fun i : Old ↦ R.yOld i < R.zOld i)
    have hs :
        Fintype.card {i : Old // R.yOld i < R.zOld i} =
          surplusCount R.yOld R.zOld := by
      simp [surplusCount, surplusSet, Fintype.card_subtype]
    have hle := surplusCount_le_card R.yOld R.zOld
    rw [hs] at hc
    omega
  have hnewPart :
      Fintype.card {j : New // ¬ R.yNew j < R.zNew j} +
          surplusCount R.yNew R.zNew = Fintype.card New := by
    have hc := Fintype.card_subtype_compl
      (p := fun j : New ↦ R.yNew j < R.zNew j)
    have hs :
        Fintype.card {j : New // R.yNew j < R.zNew j} =
          surplusCount R.yNew R.zNew := by
      simp [surplusCount, surplusSet, Fintype.card_subtype]
    have hle := surplusCount_le_card R.yNew R.zNew
    rw [hs] at hc
    omega
  omega

/-- Every reference class has a child, so class count cannot decrease. -/
theorem classCount_mono (R : RefinementData Old New) :
    Fintype.card Old ≤ Fintype.card New := by
  classical
  have hex : ∀ i : Old, ∃ j : New, R.parent j = i := by
    intro i
    let F := refinementFiber R.parent i
    have hy := R.y_conserve i
    have hF : F.Nonempty := by
      by_contra hempty
      have hzero : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hempty
      change (∑ j ∈ F, R.yNew j) = R.yOld i at hy
      rw [hzero] at hy
      simp only [Finset.sum_empty] at hy
      have hp := R.yOld_pos i
      omega
    obtain ⟨j, hj⟩ := hF
    exact ⟨j, (R.mem_refinementFiber i j).mp hj⟩
  choose representative hparent using hex
  apply Fintype.card_le_of_injective representative
  intro i k hik
  have hp := congrArg R.parent hik
  simpa [hparent] using hp

/-! ## Explicit `(q, Δ, P)` refinement credits -/

/-- Number of genuinely new reference classes created by the refinement. -/
def classRefinementCredit (_R : RefinementData Old New) : ℕ :=
  Fintype.card New - Fintype.card Old

/-- Increase in integral cross-execution deficit. -/
def deficitRefinementCredit (R : RefinementData Old New) : ℕ :=
  crossDeficit R.yNew R.zNew - crossDeficit R.yOld R.zOld

/-- The new class count is the old count plus its explicit credit. -/
theorem classCount_update (R : RefinementData Old New) :
    Fintype.card New = Fintype.card Old + R.classRefinementCredit := by
  have hq := R.classCount_mono
  unfold classRefinementCredit
  omega

/-- The new deficit is the old deficit plus its explicit credit. -/
theorem crossDeficit_update (R : RefinementData Old New) :
    crossDeficit R.yNew R.zNew =
      crossDeficit R.yOld R.zOld + R.deficitRefinementCredit := by
  have hΔ := R.crossDeficit_mono
  unfold deficitRefinementCredit
  omega

/-- Refinement translates directly into the credit inequality consumed by
the abstract prefix certificate.  In fact the class credit alone pays for
all possible growth in the number `P` of surplus coordinates; the displayed
deficit credit is harmless extra slack. -/
theorem surplus_growth_by_refinementCredits (R : RefinementData Old New) :
    surplusCount R.yNew R.zNew ≤
      surplusCount R.yOld R.zOld + R.classRefinementCredit +
        R.deficitRefinementCredit := by
  have hP := R.surplus_refinement_inequality
  have hq := R.classCount_mono
  unfold classRefinementCredit deficitRefinementCredit
  omega

/-- Both old and new frontiers satisfy the state bounds required by the
cross-execution credit when `order` is their conserved reference mass. -/
theorem refinement_state_bounds (R : RefinementData Old New) (order : ℕ)
    (hOrder : (∑ i, R.yOld i) = order) :
    Fintype.card Old ≤ order ∧
      crossDeficit R.yOld R.zOld ≤ order - Fintype.card Old ∧
      Fintype.card New ≤ order ∧
      crossDeficit R.yNew R.zNew ≤ order - Fintype.card New := by
  have hNewOrder : (∑ j, R.yNew j) = order := by
    rw [R.referenceMass_eq, hOrder]
  have hqOld := card_le_sum_of_pos R.yOld R.yOld_pos
  have hqNew := card_le_sum_of_pos R.yNew R.yNew_pos
  have hΔOld := crossDeficit_le_sum_sub_card_of_pos
    R.yOld R.zOld R.yOld_pos R.zOld_pos
  have hΔNew := crossDeficit_le_sum_sub_card_of_pos
    R.yNew R.zNew R.yNew_pos R.zNew_pos
  simpa [hOrder, hNewOrder] using And.intro hqOld
    (And.intro hΔOld (And.intro hqNew hΔNew))

/-- Every refinement weakly decreases the aggregate cross-execution credit.
This packages the monotonicities of `q`, `Δ`, and `P` into one theorem. -/
theorem crossExecutionCredit_mono (R : RefinementData Old New) (order : ℕ)
    (hOrder : (∑ i, R.yOld i) = order) :
    crossExecutionCredit order R.yNew R.zNew ≤
      crossExecutionCredit order R.yOld R.zOld := by
  obtain ⟨hqOld, hΔOld, hqNew, hΔNew⟩ :=
    R.refinement_state_bounds order hOrder
  have hq := R.classCount_mono
  have hΔ := R.crossDeficit_mono
  have hP := R.surplus_refinement_inequality
  unfold crossExecutionCredit
  omega

/-- A genuine reference-class split strictly spends aggregate credit. -/
theorem crossExecutionCredit_strict_of_classRefinement
    (R : RefinementData Old New) (order : ℕ)
    (hOrder : (∑ i, R.yOld i) = order)
    (hBranch : Fintype.card Old < Fintype.card New) :
    crossExecutionCredit order R.yNew R.zNew <
      crossExecutionCredit order R.yOld R.zOld := by
  obtain ⟨hqOld, hΔOld, hqNew, hΔNew⟩ :=
    R.refinement_state_bounds order hOrder
  have hΔ := R.crossDeficit_mono
  have hP := R.surplus_refinement_inequality
  unfold crossExecutionCredit
  omega

/-- A strict increase of the integral deficit spends aggregate credit, even
when the reference partition itself does not split. -/
theorem crossExecutionCredit_strict_of_deficitIncrease
    (R : RefinementData Old New) (order : ℕ)
    (hOrder : (∑ i, R.yOld i) = order)
    (hDeficit : crossDeficit R.yOld R.zOld <
      crossDeficit R.yNew R.zNew) :
    crossExecutionCredit order R.yNew R.zNew <
      crossExecutionCredit order R.yOld R.zOld := by
  obtain ⟨hqOld, hΔOld, hqNew, hΔNew⟩ :=
    R.refinement_state_bounds order hOrder
  have hq := R.classCount_mono
  have hP := R.surplus_refinement_inequality
  unfold crossExecutionCredit
  omega

/-- A strict loss of a surplus coordinate spends aggregate credit.  The
other two resources cannot be replenished under refinement. -/
theorem crossExecutionCredit_strict_of_surplusDecrease
    (R : RefinementData Old New) (order : ℕ)
    (hOrder : (∑ i, R.yOld i) = order)
    (hSurplus : surplusCount R.yNew R.zNew <
      surplusCount R.yOld R.zOld) :
    crossExecutionCredit order R.yNew R.zNew <
      crossExecutionCredit order R.yOld R.zOld := by
  obtain ⟨hqOld, hΔOld, hqNew, hΔNew⟩ :=
    R.refinement_state_bounds order hOrder
  have hq := R.classCount_mono
  have hΔ := R.crossDeficit_mono
  unfold crossExecutionCredit
  omega

/-- The three possible strict payments are exactly the events used by the
branching-prefix proof. -/
theorem crossExecutionCredit_strict_of_payment
    (R : RefinementData Old New) (order : ℕ)
    (hOrder : (∑ i, R.yOld i) = order)
    (hPayment :
      Fintype.card Old < Fintype.card New ∨
      crossDeficit R.yOld R.zOld < crossDeficit R.yNew R.zNew ∨
      surplusCount R.yNew R.zNew < surplusCount R.yOld R.zOld) :
    crossExecutionCredit order R.yNew R.zNew <
      crossExecutionCredit order R.yOld R.zOld := by
  rcases hPayment with hClass | hDeficit | hSurplus
  · exact R.crossExecutionCredit_strict_of_classRefinement
      order hOrder hClass
  · exact R.crossExecutionCredit_strict_of_deficitIncrease
      order hOrder hDeficit
  · exact R.crossExecutionCredit_strict_of_surplusDecrease
      order hOrder hSurplus

/-- Addition-form strict descent, convenient for summing a finite trace. -/
theorem crossExecutionCredit_add_one_le_of_classRefinement
    (R : RefinementData Old New) (order : ℕ)
    (hOrder : (∑ i, R.yOld i) = order)
    (hBranch : Fintype.card Old < Fintype.card New) :
    crossExecutionCredit order R.yNew R.zNew + 1 ≤
      crossExecutionCredit order R.yOld R.zOld := by
  exact R.crossExecutionCredit_strict_of_classRefinement order hOrder hBranch

/-! ## Strict events supplied by the matrix/history argument -/

/-- A transition makes a strict integral-deficit payment. -/
def StrictDeficitPayment (R : RefinementData Old New) : Prop :=
  crossDeficit R.yOld R.zOld < crossDeficit R.yNew R.zNew

/-- A transition makes a strict matching-mass payment. -/
def StrictMassPayment (R : RefinementData Old New) : Prop :=
  matchingMass R.zNew < matchingMass R.zOld

/-- A transition strictly increases the number of reference classes. -/
def StrictClassRefinement (_R : RefinementData Old New) : Prop :=
  Fintype.card Old < Fintype.card New

theorem deficit_add_one_le_of_payment (R : RefinementData Old New)
    (h : R.StrictDeficitPayment) :
    crossDeficit R.yOld R.zOld + 1 ≤ crossDeficit R.yNew R.zNew := by
  exact h

theorem mass_add_one_le_of_payment (R : RefinementData Old New)
    (h : R.StrictMassPayment) :
    matchingMass R.zNew + 1 ≤ matchingMass R.zOld := by
  exact h

theorem class_add_one_le_of_refinement (R : RefinementData Old New)
    (h : R.StrictClassRefinement) :
    Fintype.card Old + 1 ≤ Fintype.card New := by
  exact h

end RefinementData

end DirectedCounting
