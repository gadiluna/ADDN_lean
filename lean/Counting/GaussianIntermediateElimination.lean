import Counting.GaussianIntermediateBasis

namespace Counting.GaussianBits
open DirectedCounting.VerifiedGaussianAnchorSolver
open RationalSystem
open DirectedCounting.GaussianGeneratorCompleteness
open scoped BigOperators Matrix
variable {q : Nat}

def cleared (matrix : Augmented q ℚ) (pivot : Fin q) (rows : List (Fin q)) : Augmented q ℚ :=
  fun row col => if row = pivot then matrix row col
    else if row ∈ rows then matrix row col - matrix row (some pivot) * matrix pivot col
    else matrix row col

theorem cleared_nil (matrix : Augmented q ℚ) (pivot : Fin q) : cleared matrix pivot [] = matrix := by
  ext row column
  simp [cleared]

theorem cleared_cons (matrix : Augmented q ℚ) (pivot target : Fin q) (rows : List (Fin q))
    (normalized : matrix pivot (some pivot) = 1) :
    cleared (cleared matrix pivot [target]) pivot rows = cleared matrix pivot (target :: rows) := by
  ext row column
  by_cases pivotRow : row = pivot
  · subst row
    simp [cleared]
  · by_cases targetRow : row = target
    · subst row
      by_cases present : target ∈ rows <;>
        simp [cleared, pivotRow, present, normalized]
    · by_cases present : row ∈ rows <;>
        simp [cleared, pivotRow, targetRow, present]

theorem augmented_eliminateOne (pivot target : Fin q) (state : GaussianState q)
    (ok : state.ok = true) :
    augmented (eliminateOne pivot state target).system = cleared (augmented state.system) pivot [target] := by
  ext row column
  by_cases same : target = pivot
  · subst target
    by_cases pivotRow : row = pivot <;> simp [eliminateOne, cleared, pivotRow]
  · simp only [eliminateOne, ok, if_true, same, if_false, GaussianState.emit]
    rw [congrFun (augmented_applyRowOp state.system (.add target pivot (-state.system.coeff target pivot)) column) row]
    simp only [RowOp.transform, cleared, List.mem_singleton]
    by_cases pivotRow : row = pivot
    · subst row
      simp [Ne.symm same]
    · by_cases targetRow : row = target
      · subst row
        simp only [if_neg same]
        change augmented state.system target column + -state.system.coeff target pivot * augmented state.system pivot column =
          augmented state.system target column - state.system.coeff target pivot * augmented state.system pivot column
        ring
      · simp only [pivotRow, targetRow, if_false]

theorem augmented_eliminateRows (pivot : Fin q) (rows : List (Fin q)) (state : GaussianState q)
    (ok : state.ok = true) (normalized : state.system.coeff pivot pivot = 1) :
    augmented (eliminateRows pivot rows state).system = cleared (augmented state.system) pivot rows := by
  induction rows generalizing state with
  | nil => exact (cleared_nil _ _).symm
  | cons row rows ih =>
      change augmented (eliminateRows pivot rows (eliminateOne pivot state row)).system = _
      rw [ih (eliminateOne pivot state row) (eliminateOne_ok pivot row state ok)
        ((eliminateOne_pivot_row pivot row pivot state).trans normalized),
        augmented_eliminateOne pivot row state ok]
      exact cleared_cons _ pivot row rows normalized

theorem normalized_augmented (system : RationalSystem q) (pivot row : Fin q) (column : Option (Fin q)) :
    augmented (system.applyRowOp (.scale pivot (system.coeff pivot pivot)⁻¹)) row column =
      if row = pivot then augmented system pivot column / system.coeff pivot pivot else augmented system row column := by
  rw [congrFun (augmented_applyRowOp system (.scale pivot (system.coeff pivot pivot)⁻¹) column) row]
  simp only [RowOp.transform, div_eq_mul_inv]
  split_ifs <;> ring

/-- A partial elimination pass contains exactly old nonpivot rows or
finished nonpivot rows; the pivot row is already its final normalized row. -/
theorem actual_partial_pivot (state : GaussianState q) (pivot : Fin q) (rows : List (Fin q))
    (ok : state.ok = true) (nonzero : state.system.coeff pivot pivot ≠ 0)
    (row : Fin q) (column : Option (Fin q)) :
    augmented (eliminateRows pivot rows
      (state.emit (.scale pivot (state.system.coeff pivot pivot)⁻¹))).system row column =
      if row = pivot ∨ row ∈ rows then augmented (pivotResult state.system pivot) row column
      else augmented state.system row column := by
  have normalized : (state.emit (.scale pivot (state.system.coeff pivot pivot)⁻¹)).system.coeff pivot pivot = 1 := by
    simp [GaussianState.emit, applyRowOp, RowOp.transform, nonzero]
  have normalizedOk : (state.emit (.scale pivot (state.system.coeff pivot pivot)⁻¹)).ok = true := ok
  rw [augmented_eliminateRows pivot rows (state.emit (.scale pivot (state.system.coeff pivot pivot)⁻¹)) normalizedOk normalized]
  simp only [GaussianState.emit, cleared, normalized_augmented, augmented_pivotResult]
  by_cases pivotRow : row = pivot
  · subst row
    simp
  · by_cases present : row ∈ rows <;> simp [pivotRow, present, augmented]

theorem actual_full_pivot (state : GaussianState q) (pivot : Fin q)
    (ok : state.ok = true) (nonzero : state.system.coeff pivot pivot ≠ 0) :
    (eliminateRows pivot (List.finRange q)
      (state.emit (.scale pivot (state.system.coeff pivot pivot)⁻¹))).system = pivotResult state.system pivot := by
  have coefficients : (eliminateRows pivot (List.finRange q)
      (state.emit (.scale pivot (state.system.coeff pivot pivot)⁻¹))).system.coeff =
      (pivotResult state.system pivot).coeff := by
    ext row column
    have equal := actual_partial_pivot state pivot (List.finRange q) ok nonzero row (some column)
    simpa only [List.mem_finRange, or_true, if_true, augmented] using equal
  have rhs : (eliminateRows pivot (List.finRange q)
      (state.emit (.scale pivot (state.system.coeff pivot pivot)⁻¹))).system.rhs =
      (pivotResult state.system pivot).rhs := by
    ext row
    have equal := actual_partial_pivot state pivot (List.finRange q) ok nonzero row none
    simpa only [List.mem_finRange, or_true, if_true, augmented] using equal
  exact congrArg₂ RationalSystem.mk coefficients rhs

end Counting.GaussianBits
