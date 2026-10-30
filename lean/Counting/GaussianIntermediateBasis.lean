import Counting.GaussianIntermediateAlgebra

namespace Counting.GaussianBits
open DirectedCounting.VerifiedGaussianAnchorSolver
open RationalSystem
open scoped BigOperators Matrix
variable {q : Nat}

theorem integerBasis_pivot (original : Augmented q ℤ) (permutation : Fin q → Fin q)
    (system : RationalSystem q) (pivot : Fin q)
    (invariant : BasisInvariant original permutation pivot.val system) :
    (integerBasis original permutation (pivot.val+1)).map (Int.cast : ℤ → ℚ) =
      (integerBasis original permutation pivot.val).map (Int.cast : ℤ → ℚ) *
        pivotColumnMatrix pivot (fun row => system.coeff row pivot) := by
  have column := invariant.column_equation original permutation pivot.val system (some pivot)
  change (integerBasis original permutation pivot.val).map (Int.cast : ℤ → ℚ) *ᵥ
    (fun row => system.coeff row pivot) = (fun row => (original (permutation row) (some pivot) : ℚ)) at column
  rw [pivotColumnMatrix, Matrix.mul_updateCol, Matrix.mul_one, column]
  ext row col
  by_cases equal : col = pivot
  · subst col
    simp [integerBasis]
  · have earlier : col.val < pivot.val+1 ↔ col.val < pivot.val := by
      have unequal : col.val ≠ pivot.val := fun eq => equal (Fin.ext eq)
      omega
    simp only [Matrix.map_apply, integerBasis, earlier, Matrix.updateCol_ne equal]

theorem BasisInvariant.pivot (original : Augmented q ℤ) (permutation : Fin q → Fin q)
    (system : RationalSystem q) (pivot : Fin q)
    (invariant : BasisInvariant original permutation pivot.val system)
    (nonzero : system.coeff pivot pivot ≠ 0) :
    BasisInvariant original permutation (pivot.val+1) (pivotResult system pivot) := by
  constructor
  · have rational : ((integerBasis original permutation (pivot.val+1)).map (Int.cast : ℤ → ℚ)).det ≠ 0 := by
      rw [integerBasis_pivot original permutation system pivot invariant, Matrix.det_mul,
        ← Int.cast_det, pivotColumnMatrix_det]
      exact mul_ne_zero (by exact_mod_cast invariant.nonsingular) nonzero
    rw [← Int.cast_det] at rational
    exact_mod_cast rational
  · rw [integerBasis_pivot original permutation system pivot invariant, Matrix.mul_assoc,
      pivotResult_equation system pivot nonzero, invariant.representation]

theorem swap_preserves_frontier (pivot row : Fin q) (frontier : Nat)
    (pivotAfter : frontier ≤ pivot.val) (rowAfter : frontier ≤ row.val) (col : Fin q) :
    (Equiv.swap pivot row col).val < frontier ↔ col.val < frontier := by
  by_cases first : col = pivot
  · subst col
    simp only [Equiv.swap_apply_left]
    omega
  · by_cases second : col = row
    · subst col
      simp only [Equiv.swap_apply_right]
      omega
    · rw [Equiv.swap_apply_of_ne_of_ne first second]

theorem integerBasis_swap (original : Augmented q ℤ) (permutation : Fin q → Fin q)
    (frontier : Nat) (pivot row : Fin q)
    (pivotAfter : frontier ≤ pivot.val) (rowAfter : frontier ≤ row.val) :
    integerBasis original (permutation ∘ Equiv.swap pivot row) frontier =
      (integerBasis original permutation frontier).submatrix (Equiv.swap pivot row) (Equiv.swap pivot row) := by
  ext i j
  simp only [integerBasis, Function.comp_apply, Matrix.submatrix_apply,
    swap_preserves_frontier pivot row frontier pivotAfter rowAfter j]
  by_cases earlier : j.val < frontier
  · have first : j ≠ pivot := by intro eq; subst j; omega
    have second : j ≠ row := by intro eq; subst j; omega
    simp only [earlier, if_true, Equiv.swap_apply_of_ne_of_ne first second]
  · simp only [earlier, if_false, (Equiv.swap pivot row).injective.eq_iff]

theorem augmented_swap (system : RationalSystem q) (pivot row : Fin q) :
    augmented (system.applyRowOp (.swap pivot row)) =
      (augmented system).submatrix (Equiv.swap pivot row) id := by
  ext i column
  have columnEquation := congrFun (augmented_applyRowOp system (.swap pivot row) column) i
  rw [columnEquation]
  simp only [RowOp.transform, Matrix.submatrix_apply, id_eq, Equiv.swap_apply_def]
  split_ifs <;> rfl

theorem BasisInvariant.swap (original : Augmented q ℤ) (permutation : Fin q → Fin q)
    (frontier : Nat) (system : RationalSystem q) (pivot row : Fin q)
    (invariant : BasisInvariant original permutation frontier system)
    (pivotAfter : frontier ≤ pivot.val) (rowAfter : frontier ≤ row.val) :
    BasisInvariant original (permutation ∘ Equiv.swap pivot row) frontier
      (system.applyRowOp (.swap pivot row)) := by
  constructor
  · rw [integerBasis_swap original permutation frontier pivot row pivotAfter rowAfter,
      Matrix.det_submatrix_equiv_self]
    exact invariant.nonsingular
  · rw [integerBasis_swap original permutation frontier pivot row pivotAfter rowAfter, augmented_swap]
    change ((integerBasis original permutation frontier).map (Int.cast : ℤ → ℚ)).submatrix
        (Equiv.swap pivot row) (Equiv.swap pivot row) *
        (augmented system).submatrix (Equiv.swap pivot row) id = _
    rw [Matrix.submatrix_mul_equiv, invariant.representation]
    rfl

end Counting.GaussianBits
