import DirectedCountingFormalization.VerifiedGaussianAnchorSolver

/-!
# Completeness invariant for the deterministic Gaussian generator

The central invariant after processing the first `k` pivots is:

* columns with index below `k` are the corresponding identity columns;
* the current coefficient matrix still has injective `mulVec`.

Injectivity forces a nonzero pivot at or below the diagonal.  Otherwise the
current column is an explicit linear combination of the preceding identity
columns, producing a nonzero kernel vector.
-/

set_option warningAsError true

namespace DirectedCounting
namespace GaussianGeneratorCompleteness

open scoped BigOperators Matrix
open VerifiedGaussianAnchorSolver
open VerifiedGaussianAnchorSolver.RationalSystem

variable {q : Nat}

/-- The first `k` columns agree with the identity matrix. -/
def ProcessedColumns (A : Matrix (Fin q) (Fin q) ℚ) (k : Nat) : Prop :=
  ∀ j : Fin q, j.1 < k → ∀ r : Fin q,
    A r j = if r = j then 1 else 0

theorem processedColumns_zero_below
    {A : Matrix (Fin q) (Fin q) ℚ} {k : Nat}
    (processed : ProcessedColumns A k)
    {j r : Fin q} (hj : j.1 < k) (hr : k ≤ r.1) :
    A r j = 0 := by
  rw [processed j hj r]
  have hrj : r ≠ j := by
    intro h
    subst r
    omega
  simp [hrj]

/-- Explicit dependence vector used if a pivot column vanishes on all rows
at or below its diagonal. -/
def dependencyVector (A : Matrix (Fin q) (Fin q) ℚ) (pivot : Fin q) :
    Fin q → ℚ :=
  fun j ↦ if j = pivot then 1
    else if j.1 < pivot.1 then -A j pivot else 0

theorem dependencyVector_pivot
    (A : Matrix (Fin q) (Fin q) ℚ) (pivot : Fin q) :
    dependencyVector A pivot pivot = 1 := by
  simp [dependencyVector]

theorem dependencyVector_ne_zero
    (A : Matrix (Fin q) (Fin q) ℚ) (pivot : Fin q) :
    dependencyVector A pivot ≠ 0 := by
  intro hzero
  have hpivot := congrFun hzero pivot
  simp [dependencyVector] at hpivot

/-- If no eligible pivot exists, the explicit dependence vector is in the
kernel. -/
theorem mulVec_dependencyVector_eq_zero
    (A : Matrix (Fin q) (Fin q) ℚ) (pivot : Fin q)
    (processed : ProcessedColumns A pivot.1)
    (noPivot : ∀ r : Fin q, pivot.1 ≤ r.1 → A r pivot = 0) :
    A *ᵥ dependencyVector A pivot = 0 := by
  funext r
  unfold Matrix.mulVec dotProduct
  by_cases hr : r.1 < pivot.1
  · have hrp : r ≠ pivot := by
      intro h
      subst r
      omega
    let term : Fin q → ℚ := fun j ↦ A r j * dependencyVector A pivot j
    have hpivotMem : pivot ∈ (Finset.univ : Finset (Fin q)) := Finset.mem_univ _
    have hrMem : r ∈ (Finset.univ.erase pivot : Finset (Fin q)) := by
      simp [hrp]
    have htermPivot : term pivot = A r pivot := by
      simp [term, dependencyVector]
    have htermR : term r = -A r pivot := by
      unfold term dependencyVector
      rw [if_neg hrp, if_pos hr, processed r hr r]
      simp
    have hrest :
        (∑ j ∈ (Finset.univ.erase pivot).erase r, term j) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      have hjr : j ≠ r := (Finset.mem_erase.mp hj).1
      have hjPivot : j ≠ pivot :=
        (Finset.mem_erase.mp (Finset.mem_erase.mp hj).2).1
      change A r j * dependencyVector A pivot j = 0
      by_cases hjlt : j.1 < pivot.1
      · rw [processed j hjlt r]
        simp [dependencyVector, hjPivot, hjlt, Ne.symm hjr]
      · simp [dependencyVector, hjPivot, hjlt]
    calc
      (∑ j, A r j * dependencyVector A pivot j) =
          term pivot + ∑ j ∈ (Finset.univ.erase pivot), term j := by
        exact (Finset.add_sum_erase Finset.univ term hpivotMem).symm
      _ = term pivot +
          (term r + ∑ j ∈ (Finset.univ.erase pivot).erase r, term j) := by
        rw [Finset.add_sum_erase (Finset.univ.erase pivot) term hrMem]
      _ = A r pivot + (-A r pivot) + 0 := by
        rw [htermPivot, htermR, hrest]
        ring
      _ = 0 := by ring
  · have hrge : pivot.1 ≤ r.1 := by omega
    apply Finset.sum_eq_zero
    intro j _hj
    by_cases hjPivot : j = pivot
    · subst j
      simp [dependencyVector, noPivot r hrge]
    · by_cases hjlt : j.1 < pivot.1
      · have hrj : r ≠ j := by
          intro h
          subst r
          omega
        change A r j * dependencyVector A pivot j = 0
        rw [processed j hjlt r]
        simp [dependencyVector, hjPivot, hjlt, hrj]
      · simp [dependencyVector, hjPivot, hjlt]

/-- An injective matrix with processed earlier columns has an eligible pivot. -/
theorem exists_eligible_pivot
    (A : Matrix (Fin q) (Fin q) ℚ) (pivot : Fin q)
    (processed : ProcessedColumns A pivot.1)
    (injective : Function.Injective A.mulVec) :
    ∃ r : Fin q, pivot.1 ≤ r.1 ∧ A r pivot ≠ 0 := by
  by_contra hnone
  push Not at hnone
  have hkernel := mulVec_dependencyVector_eq_zero A pivot processed hnone
  have heq : dependencyVector A pivot = 0 := by
    apply injective
    rw [hkernel, Matrix.mulVec_zero]
  exact dependencyVector_ne_zero A pivot heq

theorem findPivot?_some_property
    (system : RationalSystem q) (pivot row : Fin q)
    (found : findPivot? system pivot = some row) :
    pivot.1 ≤ row.1 ∧ system.coeff row pivot ≠ 0 := by
  unfold findPivot? at found
  have hp := List.find?_some found
  simpa using hp

theorem findPivot?_exists_of_injective
    (system : RationalSystem q) (pivot : Fin q)
    (processed : ProcessedColumns system.coeff pivot.1)
    (injective : Function.Injective system.coeff.mulVec) :
    ∃ row, findPivot? system pivot = some row := by
  obtain ⟨row, hrow, hnonzero⟩ :=
    exists_eligible_pivot system.coeff pivot processed injective
  have hpredicate :
      decide (pivot.1 ≤ row.1 ∧ system.coeff row pivot ≠ 0) = true := by
    simp [hrow, hnonzero]
  have hisSome :
      ((List.finRange q).find? fun r ↦
        decide (pivot.1 ≤ r.1 ∧ system.coeff r pivot ≠ 0)).isSome := by
    rw [← Fin.find?_eq_find?_finRange]
    exact Fin.isSome_find?_of_eq_true hpredicate
  cases hfound : findPivot? system pivot with
  | none =>
      unfold findPivot? at hfound
      rw [hfound] at hisSome
      simp at hisSome
  | some found => exact ⟨found, rfl⟩

/-! ## Elementary-operation invariants -/

/-- Applying a valid row operation preserves injectivity of matrix-vector
multiplication. -/
theorem applyRowOp_coeff_mulVec_injective
    (system : RationalSystem q) (op : RowOp q) (valid : op.Valid)
    (injective : Function.Injective system.coeff.mulVec) :
    Function.Injective (system.applyRowOp op).coeff.mulVec := by
  intro x y hxy
  apply injective
  apply op.transform_injective valid
  simpa only [system.applyRowOp_mulVec op x,
    system.applyRowOp_mulVec op y] using hxy

/-- Swapping two rows at or below the frontier cannot modify a processed
column. -/
theorem processedColumns_apply_swap
    (system : RationalSystem q) {k : Nat} (processed : ProcessedColumns system.coeff k)
    (i j : Fin q) (hi : k ≤ i.1) (hj : k ≤ j.1) :
    ProcessedColumns (system.applyRowOp (.swap i j)).coeff k := by
  intro col hcol r
  change (if r = i then system.coeff j col
    else if r = j then system.coeff i col else system.coeff r col) = _
  by_cases hri : r = i
  · subst r
    have hicol : i ≠ col := by
      intro h
      subst i
      omega
    rw [if_pos rfl, processedColumns_zero_below processed hcol hj]
    simp [hicol]
  · by_cases hrj : r = j
    · subst r
      have hjcol : j ≠ col := by
        intro h
        subst j
        omega
      rw [if_neg hri, if_pos rfl,
        processedColumns_zero_below processed hcol hi]
      simp [hjcol]
    · rw [if_neg hri, if_neg hrj, processed col hcol r]

/-- Scaling a row at or below the frontier cannot modify a processed
column. -/
theorem processedColumns_apply_scale
    (system : RationalSystem q) {k : Nat} (processed : ProcessedColumns system.coeff k)
    (i : Fin q) (hi : k ≤ i.1) (c : ℚ) :
    ProcessedColumns (system.applyRowOp (.scale i c)).coeff k := by
  intro col hcol r
  change (if r = i then c * system.coeff i col else system.coeff r col) = _
  by_cases hri : r = i
  · subst r
    have hicol : i ≠ col := by
      intro h
      subst i
      omega
    rw [if_pos rfl, processedColumns_zero_below processed hcol hi]
    simp [hicol]
  · rw [if_neg hri, processed col hcol r]

/-- Adding a multiple of a source row at or below the frontier cannot modify
a processed column, regardless of the target row. -/
theorem processedColumns_apply_add
    (system : RationalSystem q) {k : Nat} (processed : ProcessedColumns system.coeff k)
    (target source : Fin q) (hsource : k ≤ source.1) (c : ℚ) :
    ProcessedColumns (system.applyRowOp (.add target source c)).coeff k := by
  intro col hcol r
  change (if r = target then
    system.coeff target col + c * system.coeff source col
    else system.coeff r col) = _
  by_cases hrt : r = target
  · subst r
    rw [if_pos rfl, processedColumns_zero_below processed hcol hsource,
      processed col hcol target]
    simp
  · rw [if_neg hrt, processed col hcol r]

/-! ## Elimination-loop invariants -/

theorem eliminateOne_ok
    (pivot row : Fin q) (state : GaussianState q)
    (ok : state.ok = true) :
    (eliminateOne pivot state row).ok = true := by
  by_cases hrow : row = pivot <;>
    simp [eliminateOne, ok, hrow, GaussianState.emit]

theorem eliminateRows_ok
    (pivot : Fin q) (rows : List (Fin q)) (state : GaussianState q)
    (ok : state.ok = true) :
    (eliminateRows pivot rows state).ok = true := by
  induction rows generalizing state with
  | nil => simpa [eliminateRows]
  | cons row rows ih =>
      change (eliminateRows pivot rows
        (eliminateOne pivot state row)).ok = true
      exact ih (state := eliminateOne pivot state row)
        (eliminateOne_ok pivot row state ok)

theorem eliminateOne_processedColumns
    (pivot row : Fin q) (state : GaussianState q) {k : Nat}
    (hpivot : k ≤ pivot.1)
    (processed : ProcessedColumns state.system.coeff k) :
    ProcessedColumns (eliminateOne pivot state row).system.coeff k := by
  by_cases ok : state.ok = true
  · by_cases hrow : row = pivot
    · simpa [eliminateOne, ok, hrow]
    · simpa [eliminateOne, ok, hrow, GaussianState.emit] using
        processedColumns_apply_add state.system processed row pivot hpivot
          (-state.system.coeff row pivot)
  · simpa [eliminateOne, ok]

theorem eliminateRows_processedColumns
    (pivot : Fin q) (rows : List (Fin q)) (state : GaussianState q) {k : Nat}
    (hpivot : k ≤ pivot.1)
    (processed : ProcessedColumns state.system.coeff k) :
    ProcessedColumns (eliminateRows pivot rows state).system.coeff k := by
  induction rows generalizing state with
  | nil => simpa [eliminateRows]
  | cons row rows ih =>
      change ProcessedColumns
        (eliminateRows pivot rows (eliminateOne pivot state row)).system.coeff k
      exact ih (state := eliminateOne pivot state row)
        (eliminateOne_processedColumns pivot row state hpivot processed)

theorem eliminateOne_coeff_mulVec_injective
    (pivot row : Fin q) (state : GaussianState q)
    (injective : Function.Injective state.system.coeff.mulVec) :
    Function.Injective (eliminateOne pivot state row).system.coeff.mulVec := by
  by_cases ok : state.ok = true
  · by_cases hrow : row = pivot
    · simpa [eliminateOne, ok, hrow]
    · simpa [eliminateOne, ok, hrow, GaussianState.emit] using
        applyRowOp_coeff_mulVec_injective state.system
          (.add row pivot (-state.system.coeff row pivot)) hrow injective
  · simpa [eliminateOne, ok]

theorem eliminateRows_coeff_mulVec_injective
    (pivot : Fin q) (rows : List (Fin q)) (state : GaussianState q)
    (injective : Function.Injective state.system.coeff.mulVec) :
    Function.Injective
      (eliminateRows pivot rows state).system.coeff.mulVec := by
  induction rows generalizing state with
  | nil => simpa [eliminateRows]
  | cons row rows ih =>
      change Function.Injective
        (eliminateRows pivot rows
          (eliminateOne pivot state row)).system.coeff.mulVec
      exact ih (state := eliminateOne pivot state row)
        (eliminateOne_coeff_mulVec_injective pivot row state injective)

/-- Eliminating a different target leaves a watched row unchanged. -/
theorem eliminateOne_system_coeff_of_ne
    (pivot row watched col : Fin q) (state : GaussianState q)
    (hne : watched ≠ row) :
    (eliminateOne pivot state row).system.coeff watched col =
      state.system.coeff watched col := by
  by_cases ok : state.ok = true
  · by_cases hrow : row = pivot
    · simp [eliminateOne, ok, hrow]
    · simp [eliminateOne, ok, hrow, GaussianState.emit,
        RationalSystem.applyRowOp, RowOp.transform, hne]
  · simp [eliminateOne, ok]

/-- No elimination step ever changes the pivot row. -/
theorem eliminateOne_pivot_row
    (pivot row col : Fin q) (state : GaussianState q) :
    (eliminateOne pivot state row).system.coeff pivot col =
      state.system.coeff pivot col := by
  by_cases hrow : row = pivot
  · subst row
    simp [eliminateOne]
  · exact eliminateOne_system_coeff_of_ne pivot row pivot col state (Ne.symm hrow)

theorem eliminateRows_pivot_row
    (pivot col : Fin q) (rows : List (Fin q)) (state : GaussianState q) :
    (eliminateRows pivot rows state).system.coeff pivot col =
      state.system.coeff pivot col := by
  induction rows generalizing state with
  | nil => simp [eliminateRows]
  | cons row rows ih =>
      change (eliminateRows pivot rows
        (eliminateOne pivot state row)).system.coeff pivot col = _
      rw [ih, eliminateOne_pivot_row]

/-- If a watched row does not occur in the supplied list, the entire
elimination fold leaves that row unchanged. -/
theorem eliminateRows_system_coeff_of_not_mem
    (pivot watched col : Fin q) (rows : List (Fin q))
    (state : GaussianState q) (notMem : watched ∉ rows) :
    (eliminateRows pivot rows state).system.coeff watched col =
      state.system.coeff watched col := by
  induction rows generalizing state with
  | nil => simp [eliminateRows]
  | cons row rows ih =>
      have hne : watched ≠ row := by
        intro h
        subst watched
        exact notMem (by simp)
      have hnotTail : watched ∉ rows := by
        intro h
        exact notMem (by simp [h])
      change (eliminateRows pivot rows
        (eliminateOne pivot state row)).system.coeff watched col = _
      rw [ih (state := eliminateOne pivot state row) hnotTail,
        eliminateOne_system_coeff_of_ne pivot row watched col state hne]

/-- Once the pivot row is normalized, eliminating a distinct target makes
the target's pivot entry exactly zero. -/
theorem eliminateOne_target_pivot_eq_zero
    (pivot row : Fin q) (state : GaussianState q)
    (ok : state.ok = true) (hrow : row ≠ pivot)
    (normalized : state.system.coeff pivot pivot = 1) :
    (eliminateOne pivot state row).system.coeff row pivot = 0 := by
  simp [eliminateOne, ok, hrow, GaussianState.emit,
    RationalSystem.applyRowOp, RowOp.transform, normalized]

/-- A full elimination pass turns a normalized pivot column into the
corresponding identity column. -/
theorem eliminateRows_finRange_pivot_column
    (pivot : Fin q) (state : GaussianState q)
    (ok : state.ok = true)
    (normalized : state.system.coeff pivot pivot = 1) :
    ∀ r : Fin q,
      (eliminateRows pivot (List.finRange q) state).system.coeff r pivot =
        if r = pivot then 1 else 0 := by
  intro r
  by_cases hr : r = pivot
  · subst r
    rw [if_pos rfl, eliminateRows_pivot_row]
    exact normalized
  · rw [if_neg hr]
    obtain ⟨before, after, hsplit⟩ :=
      List.mem_iff_append.mp (List.mem_finRange r)
    have hnodup : (before ++ r :: after).Nodup := by
      rw [← hsplit]
      exact List.nodup_finRange q
    have rNotMemAfter : r ∉ after :=
      (List.nodup_cons.mp
        (List.Nodup.of_append_right hnodup)).1
    let beforeState := eliminateRows pivot before state
    have beforeOk : beforeState.ok = true :=
      eliminateRows_ok pivot before state ok
    have beforeNormalized :
        beforeState.system.coeff pivot pivot = 1 := by
      simpa only [beforeState] using
        (eliminateRows_pivot_row pivot pivot before state).trans normalized
    let rowState := eliminateOne pivot beforeState r
    have rowZero : rowState.system.coeff r pivot = 0 := by
      exact eliminateOne_target_pivot_eq_zero pivot r beforeState
        beforeOk hr beforeNormalized
    have suffixUnchanged :
        (eliminateRows pivot after rowState).system.coeff r pivot =
          rowState.system.coeff r pivot :=
      eliminateRows_system_coeff_of_not_mem pivot r pivot after rowState
        rNotMemAfter
    have hfold :
        eliminateRows pivot (List.finRange q) state =
          eliminateRows pivot after rowState := by
      simp only [eliminateRows, hsplit, List.foldl_append, List.foldl_cons,
        beforeState, rowState]
    rw [hfold, suffixUnchanged, rowZero]

theorem processedColumns_succ_of_pivot_column
    (A : Matrix (Fin q) (Fin q) ℚ) (pivot : Fin q)
    (processed : ProcessedColumns A pivot.1)
    (pivotColumn : ∀ r : Fin q,
      A r pivot = if r = pivot then 1 else 0) :
    ProcessedColumns A (pivot.1 + 1) := by
  intro col hcol r
  by_cases hbefore : col.1 < pivot.1
  · exact processed col hbefore r
  · have hval : col.1 = pivot.1 := by omega
    have hcolPivot : col = pivot := Fin.ext hval
    subst col
    exact pivotColumn r

/-! ## A complete pivot stage -/

/-- On an injective matrix, one pivot stage succeeds, extends the identity
prefix by one column, and preserves injectivity. -/
theorem pivotStep_invariant
    (state : GaussianState q) (pivot : Fin q)
    (ok : state.ok = true)
    (processed : ProcessedColumns state.system.coeff pivot.1)
    (injective : Function.Injective state.system.coeff.mulVec) :
    let next := pivotStep state pivot
    next.ok = true ∧
      ProcessedColumns next.system.coeff (pivot.1 + 1) ∧
      Function.Injective next.system.coeff.mulVec := by
  obtain ⟨row, found⟩ :=
    findPivot?_exists_of_injective state.system pivot processed injective
  have rowProperty := findPivot?_some_property state.system pivot row found
  let swapped := state.emit (.swap pivot row)
  have swappedValue :
      swapped.system.coeff pivot pivot = state.system.coeff row pivot := by
    simp [swapped, GaussianState.emit, RationalSystem.applyRowOp,
      RowOp.transform]
  have swappedNonzero : swapped.system.coeff pivot pivot ≠ 0 := by
    rw [swappedValue]
    exact rowProperty.2
  have swappedProcessed :
      ProcessedColumns swapped.system.coeff pivot.1 := by
    simpa only [swapped, GaussianState.emit] using
      processedColumns_apply_swap state.system processed pivot row
        (Nat.le_refl _) rowProperty.1
  have swappedInjective :
      Function.Injective swapped.system.coeff.mulVec := by
    simpa only [swapped, GaussianState.emit] using
      applyRowOp_coeff_mulVec_injective state.system (.swap pivot row)
        (by simp [RowOp.Valid]) injective
  let normalized := swapped.emit
    (.scale pivot (swapped.system.coeff pivot pivot)⁻¹)
  have normalizedOk : normalized.ok = true := by
    simp [normalized, swapped, GaussianState.emit, ok]
  have normalizedProcessed :
      ProcessedColumns normalized.system.coeff pivot.1 := by
    simpa only [normalized, GaussianState.emit] using
      processedColumns_apply_scale swapped.system swappedProcessed pivot
        (Nat.le_refl _) (swapped.system.coeff pivot pivot)⁻¹
  have normalizedInjective :
      Function.Injective normalized.system.coeff.mulVec := by
    simpa only [normalized, GaussianState.emit] using
      applyRowOp_coeff_mulVec_injective swapped.system
        (.scale pivot (swapped.system.coeff pivot pivot)⁻¹)
        (by simpa [RowOp.Valid] using inv_ne_zero swappedNonzero)
        swappedInjective
  have normalizedPivot : normalized.system.coeff pivot pivot = 1 := by
    simp [normalized, GaussianState.emit, RationalSystem.applyRowOp,
      RowOp.transform, swappedNonzero]
  let next := eliminateRows pivot (List.finRange q) normalized
  have nextOk : next.ok = true :=
    eliminateRows_ok pivot (List.finRange q) normalized normalizedOk
  have nextProcessedBefore :
      ProcessedColumns next.system.coeff pivot.1 :=
    eliminateRows_processedColumns pivot (List.finRange q) normalized
      (Nat.le_refl _) normalizedProcessed
  have nextInjective : Function.Injective next.system.coeff.mulVec :=
    eliminateRows_coeff_mulVec_injective pivot (List.finRange q)
      normalized normalizedInjective
  have nextPivotColumn : ∀ r : Fin q,
      next.system.coeff r pivot = if r = pivot then 1 else 0 := by
    exact eliminateRows_finRange_pivot_column pivot normalized normalizedOk
      normalizedPivot
  have nextProcessed :
      ProcessedColumns next.system.coeff (pivot.1 + 1) :=
    processedColumns_succ_of_pivot_column next.system.coeff pivot
      nextProcessedBefore nextPivotColumn
  have stepEq : pivotStep state pivot = next := by
    simp [pivotStep, ok, found, swapped, swappedNonzero, normalized, next]
  rw [stepEq]
  exact ⟨nextOk, nextProcessed, nextInjective⟩

/-! ## Iterating the ordered pivot list -/

/-- The values of the pivots are `k, k+1, ...` in list order. -/
def ConsecutiveFrom (k : Nat) (pivots : List (Fin q)) : Prop :=
  pivots.map (fun pivot ↦ pivot.1) =
    List.range' k pivots.length

theorem consecutiveFrom_cons
    {k : Nat} {pivot : Fin q} {pivots : List (Fin q)}
    (consecutive : ConsecutiveFrom k (pivot :: pivots)) :
    pivot.1 = k ∧ ConsecutiveFrom (k + 1) pivots := by
  unfold ConsecutiveFrom at consecutive ⊢
  simp only [List.map_cons, List.length_cons, List.range'_succ] at consecutive
  exact ⟨List.cons.inj consecutive |>.1, List.cons.inj consecutive |>.2⟩

theorem consecutiveFrom_finRange :
    ConsecutiveFrom 0 (List.finRange q) := by
  unfold ConsecutiveFrom
  rw [List.map_coe_finRange_eq_range, List.length_finRange,
    List.range_eq_range']

theorem foldl_pivotStep_invariant
    (pivots : List (Fin q)) (k : Nat)
    (consecutive : ConsecutiveFrom k pivots)
    (state : GaussianState q)
    (ok : state.ok = true)
    (processed : ProcessedColumns state.system.coeff k)
    (injective : Function.Injective state.system.coeff.mulVec) :
    let final := pivots.foldl pivotStep state
    final.ok = true ∧
      ProcessedColumns final.system.coeff (k + pivots.length) ∧
      Function.Injective final.system.coeff.mulVec := by
  induction pivots generalizing k state with
  | nil =>
      simpa using And.intro ok (And.intro processed injective)
  | cons pivot pivots ih =>
      obtain ⟨pivotValue, tailConsecutive⟩ :=
        consecutiveFrom_cons consecutive
      have processedAtPivot :
          ProcessedColumns state.system.coeff pivot.1 := by
        simpa only [pivotValue] using processed
      obtain ⟨stepOk, stepProcessed, stepInjective⟩ :=
        pivotStep_invariant state pivot ok processedAtPivot injective
      have stepProcessedAtNext :
          ProcessedColumns (pivotStep state pivot).system.coeff (k + 1) := by
        simpa only [pivotValue] using stepProcessed
      have tailResult := ih (k := k + 1)
        tailConsecutive (state := pivotStep state pivot)
        stepOk stepProcessedAtNext stepInjective
      have frontierEq : k + 1 + pivots.length =
          k + (pivots.length + 1) := by omega
      rw [frontierEq] at tailResult
      simpa only [List.foldl_cons, List.length_cons] using tailResult

theorem processedColumns_full_eq_one
    (A : Matrix (Fin q) (Fin q) ℚ)
    (processed : ProcessedColumns A q) :
    A = 1 := by
  ext r col
  rw [processed col col.isLt r]
  simp [Matrix.one_apply]

/-- The deterministic loop succeeds and reaches the identity on every
injective square rational system. -/
theorem runGaussian_ok_and_coeff_eq_one
    (system : RationalSystem q)
    (injective : Function.Injective system.coeff.mulVec) :
    (runGaussian system).ok = true ∧
      (runGaussian system).system.coeff = 1 := by
  let initial : GaussianState q :=
    { system := system, opsRev := [], ok := true }
  have initialProcessed : ProcessedColumns initial.system.coeff 0 := by
    intro col hcol
    omega
  have initialInjective :
      Function.Injective initial.system.coeff.mulVec := by
    simpa only [initial] using injective
  have result := foldl_pivotStep_invariant (List.finRange q) 0
    consecutiveFrom_finRange initial rfl initialProcessed initialInjective
  have result' :
      (runGaussian system).ok = true ∧
        ProcessedColumns (runGaussian system).system.coeff q ∧
        Function.Injective (runGaussian system).system.coeff.mulVec := by
    simpa only [runGaussian, initial, List.length_finRange,
      Nat.zero_add] using result
  exact ⟨result'.1,
    processedColumns_full_eq_one _ result'.2.1⟩

/-! ## Replay certification of the generated transcript -/

theorem replay_append
    (system : RationalSystem q) (first second : List (RowOp q)) :
    replay system (first ++ second) =
      replay (replay system first) second := by
  induction first generalizing system with
  | nil => rfl
  | cons op first ih =>
      simp only [List.cons_append, replay]
      exact ih (system.applyRowOp op)

/-- The reverse operation accumulator is certified relative to the original
input system. -/
def StateCertified (initial : RationalSystem q)
    (state : GaussianState q) : Prop :=
  TranscriptValid state.opsRev.reverse ∧
    replay initial state.opsRev.reverse = state.system

theorem initial_stateCertified (system : RationalSystem q) :
    StateCertified system
      ({ system := system, opsRev := [], ok := true } : GaussianState q) := by
  simp [StateCertified, TranscriptValid, replay]

theorem stateCertified_emit
    (initial : RationalSystem q) (state : GaussianState q) (op : RowOp q)
    (certified : StateCertified initial state) (valid : op.Valid) :
    StateCertified initial (state.emit op) := by
  constructor
  · change List.Forall RowOp.Valid (op :: state.opsRev).reverse
    rw [List.reverse_cons]
    rw [List.forall_append]
    exact ⟨certified.1, by simp [valid]⟩
  · unfold StateCertified at certified
    simp only [GaussianState.emit, List.reverse_cons]
    rw [replay_append, certified.2]
    rfl

theorem stateCertified_fail
    (initial : RationalSystem q) (state : GaussianState q)
    (certified : StateCertified initial state) :
    StateCertified initial state.fail := by
  simpa [StateCertified, GaussianState.fail] using certified

theorem eliminateOne_stateCertified
    (initial : RationalSystem q) (pivot row : Fin q)
    (state : GaussianState q)
    (certified : StateCertified initial state) :
    StateCertified initial (eliminateOne pivot state row) := by
  by_cases ok : state.ok = true
  · by_cases hrow : row = pivot
    · simpa [eliminateOne, ok, hrow]
    · simpa [eliminateOne, ok, hrow] using
        stateCertified_emit initial state
          (.add row pivot (-state.system.coeff row pivot)) certified hrow
  · simpa [eliminateOne, ok]

theorem eliminateRows_stateCertified
    (initial : RationalSystem q) (pivot : Fin q)
    (rows : List (Fin q)) (state : GaussianState q)
    (certified : StateCertified initial state) :
    StateCertified initial (eliminateRows pivot rows state) := by
  induction rows generalizing state with
  | nil => simpa [eliminateRows]
  | cons row rows ih =>
      change StateCertified initial
        (eliminateRows pivot rows (eliminateOne pivot state row))
      exact ih (state := eliminateOne pivot state row)
        (eliminateOne_stateCertified initial pivot row state certified)

theorem pivotStep_stateCertified
    (initial : RationalSystem q) (state : GaussianState q)
    (pivot : Fin q) (certified : StateCertified initial state) :
    StateCertified initial (pivotStep state pivot) := by
  by_cases ok : state.ok = true
  · cases found : findPivot? state.system pivot with
    | none =>
        simpa [pivotStep, ok, found] using
          stateCertified_fail initial state certified
    | some row =>
        let swapped := state.emit (.swap pivot row)
        have swappedCertified : StateCertified initial swapped := by
          exact stateCertified_emit initial state (.swap pivot row) certified
            (by simp [RowOp.Valid])
        by_cases value : swapped.system.coeff pivot pivot = 0
        · simpa [pivotStep, ok, found, swapped, value] using
            stateCertified_fail initial swapped swappedCertified
        · let normalized := swapped.emit
              (.scale pivot (swapped.system.coeff pivot pivot)⁻¹)
          have normalizedCertified : StateCertified initial normalized := by
            exact stateCertified_emit initial swapped
              (.scale pivot (swapped.system.coeff pivot pivot)⁻¹)
              swappedCertified
              (by simpa [RowOp.Valid] using inv_ne_zero value)
          simpa [pivotStep, ok, found, swapped, value, normalized] using
            eliminateRows_stateCertified initial pivot (List.finRange q)
              normalized normalizedCertified
  · simpa [pivotStep, ok]

theorem foldl_pivotStep_stateCertified
    (initial : RationalSystem q) (pivots : List (Fin q))
    (state : GaussianState q) (certified : StateCertified initial state) :
    StateCertified initial (pivots.foldl pivotStep state) := by
  induction pivots generalizing state with
  | nil => simpa
  | cons pivot pivots ih =>
      exact ih (state := pivotStep state pivot)
        (pivotStep_stateCertified initial state pivot certified)

theorem runGaussian_stateCertified (system : RationalSystem q) :
    StateCertified system (runGaussian system) := by
  exact foldl_pivotStep_stateCertified system (List.finRange q)
    ({ system := system, opsRev := [], ok := true } : GaussianState q)
    (initial_stateCertified system)

/-! ## Generic and anchor-specific completeness -/

/-- Every injective square rational system is accepted by the independently
replayed Gaussian transcript. -/
theorem generatorCompleteFor_of_coeff_mulVec_injective
    (system : RationalSystem q)
    (injective : Function.Injective system.coeff.mulVec) :
    GeneratorCompleteFor system := by
  let final := runGaussian system
  have finalProperties := runGaussian_ok_and_coeff_eq_one system injective
  have certified := runGaussian_stateCertified system
  have verified :
      system.verifyTranscript final.opsRev.reverse =
        some final.system.rhs := by
    unfold RationalSystem.verifyTranscript
    simp [final, certified.1, certified.2,
      finalProperties.2]
  refine ⟨final.system.rhs, ?_⟩
  unfold RationalSystem.solve? RationalSystem.generate
  simp [final, finalProperties.1, verified]

/-- A valid integral anchor makes the normal matrix injective, so the
deterministic Gaussian solver is complete on every valid anchor instance. -/
theorem anchorSystem_generatorCompleteFor
    {candidate : Nat}
    (A : IntegralAnchorInstance q)
    (output : IntegralAnchorInstance.Output q candidate)
    (valid : A.Valid output) :
    GeneratorCompleteFor (anchorSystem A) := by
  apply generatorCompleteFor_of_coeff_mulVec_injective
  exact ExactAnchorSolver.normalMatrix_mulVec_injective A output valid

/-- Completeness plus uniqueness identifies the exact rational vector
returned by the replay-checked solver. -/
theorem solveAnchor?_eq_some_natCast
    {candidate : Nat}
    (A : IntegralAnchorInstance q)
    (output : IntegralAnchorInstance.Output q candidate)
    (valid : A.Valid output) :
    solveAnchor? A = some (fun i ↦ (output.weight i : ℚ)) := by
  obtain ⟨x, accepted⟩ := anchorSystem_generatorCompleteFor A output valid
  have exactValue :=
    solveAnchor?_eq_natCast_of_some A output valid x accepted
  rw [exactValue] at accepted
  exact accepted

/-- The executable natural-number wrapper is therefore complete, not only
sound, on every valid integral anchor. -/
theorem solveAnchorNat?_eq_some
    {candidate : Nat}
    (A : IntegralAnchorInstance q)
    (output : IntegralAnchorInstance.Output q candidate)
    (valid : A.Valid output) :
    solveAnchorNat? A = some output.weight := by
  unfold solveAnchorNat?
  rw [solveAnchor?_eq_some_natCast A output valid]
  simp [ExactAnchorSolver.rationalVectorToNat?_natCast]

end GaussianGeneratorCompleteness
end DirectedCounting
