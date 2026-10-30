import Counting.GaussianOutputBounds
import Counting.StoredGaussian

/-! A bounded integer basis for every completed Gauss--Jordan frontier.
The basis has original pivot columns and identity columns elsewhere;
Cramer's rule then controls every current coefficient and right-hand side,
including the rows below the frontier. The following modules establish
this invariant for the actual generator and its transcript prefixes. -/
namespace Counting.GaussianBits
open DirectedCounting.VerifiedGaussianAnchorSolver
open RationalSystem
open scoped BigOperators Matrix

variable {q : Nat}
abbrev Augmented (q : Nat) (R : Type) := Matrix (Fin q) (Option (Fin q)) R

def augmented (system : RationalSystem q) : Augmented q ℚ :=
  fun row column => match column with | none => system.rhs row | some col => system.coeff row col

def integralSystem (original : Augmented q ℤ) : RationalSystem q :=
  ⟨fun i j => (original i (some j) : ℚ), fun i => (original i none : ℚ)⟩

theorem augmented_integral (original : Augmented q ℤ) :
    augmented (integralSystem original) = original.map (Int.cast : ℤ → ℚ) := by
  ext row column
  cases column <;> rfl

theorem augmented_applyRowOp (system : RationalSystem q) (op : RowOp q) (column : Option (Fin q)) :
    (fun row => augmented (system.applyRowOp op) row column) =
      op.transform (fun row => augmented system row column) := by cases column <;> rfl

def integerBasis (original : Augmented q ℤ) (permutation : Fin q → Fin q) (frontier : Nat) :
    Matrix (Fin q) (Fin q) ℤ :=
  fun row col => if col.val < frontier then original (permutation row) (some col)
    else if row = col then 1 else 0

structure BasisInvariant (original : Augmented q ℤ) (permutation : Fin q → Fin q)
    (frontier : Nat) (system : RationalSystem q) : Prop where
  nonsingular : (integerBasis original permutation frontier).det ≠ 0
  representation : (integerBasis original permutation frontier).map (Int.cast : ℤ → ℚ) * augmented system =
    (original.submatrix permutation id).map (Int.cast : ℤ → ℚ)

theorem integerBasis_zero (original : Augmented q ℤ) (permutation : Fin q → Fin q) :
    integerBasis original permutation 0 = 1 := by ext row col; simp [integerBasis, Matrix.one_apply]

theorem basis_initial (original : Augmented q ℤ) : BasisInvariant original id 0 (integralSystem original) := by
  constructor
  · rw [integerBasis_zero, Matrix.det_one]
    exact one_ne_zero
  · rw [integerBasis_zero, augmented_integral]
    simp

theorem integerBasis_bound (original : Augmented q ℤ) (permutation : Fin q → Fin q)
    (frontier M : Nat) (bounded : ∀ i c, (original i c).natAbs ≤ M) (i j : Fin q) :
    (integerBasis original permutation frontier i j).natAbs ≤ max M 1 := by
  by_cases earlier : j.val < frontier
  · simpa only [integerBasis, earlier, if_true] using
      (bounded (permutation i) (some j)).trans (le_max_left M 1)
  · by_cases diagonal : i = j
    · simp only [integerBasis, earlier, if_false, diagonal, if_true, Int.natAbs_one]
      exact le_max_right _ _
    · simp only [integerBasis, earlier, diagonal, if_false, Int.natAbs_zero, Nat.zero_le]

theorem BasisInvariant.column_equation (original : Augmented q ℤ) (permutation : Fin q → Fin q)
    (frontier : Nat) (system : RationalSystem q) (invariant : BasisInvariant original permutation frontier system)
    (column : Option (Fin q)) :
    (integerBasis original permutation frontier).map (Int.cast : ℤ → ℚ) *ᵥ
      (fun row => augmented system row column) = fun row => (original (permutation row) column : ℚ) := by
  funext row
  exact congrFun (congrFun invariant.representation row) column

/-- One bound controls coefficients and the augmented right-hand side.
The entries are quotients of determinants of actual bounded integer bases. -/
theorem BasisInvariant.entry_bits (original : Augmented q ℤ) (permutation : Fin q → Fin q)
    (frontier : Nat) (system : RationalSystem q) (invariant : BasisInvariant original permutation frontier system)
    (M : Nat) (bounded : ∀ i c, (original i c).natAbs ≤ M)
    (row : Fin q) (column : Option (Fin q)) :
    (augmented system row column).num.natAbs.size + (augmented system row column).den.size ≤
      2 * (q * (q.size + (max M 1).size) + 1) := by
  exact integer_solution_bits q (max M 1) (integerBasis original permutation frontier)
    (fun i => original (permutation i) column) (fun i => augmented system i column)
    invariant.nonsingular (invariant.column_equation original permutation frontier system column)
    (integerBasis_bound original permutation frontier M bounded)
    (fun i => (bounded (permutation i) column).trans (le_max_left _ _)) row

def pivotColumnMatrix (pivot : Fin q) (column : Fin q → ℚ) : Matrix (Fin q) (Fin q) ℚ :=
  (1 : Matrix (Fin q) (Fin q) ℚ).updateCol pivot column

theorem pivotColumnMatrix_det (pivot : Fin q) (column : Fin q → ℚ) :
    (pivotColumnMatrix pivot column).det = column pivot := by
  change Matrix.cramer (1 : Matrix (Fin q) (Fin q) ℚ) column pivot = _
  rw [Matrix.cramer_eq_adjugate_mulVec, Matrix.adjugate_one, Matrix.one_mulVec]

theorem pivotColumnMatrix_mulVec (pivot : Fin q) (column vector : Fin q → ℚ) (row : Fin q) :
    (pivotColumnMatrix pivot column *ᵥ vector) row =
      if row = pivot then column row * vector pivot else vector row + column row * vector pivot := by
  classical
  change (∑ j, pivotColumnMatrix pivot column row j * vector j) = _
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ pivot)]
  have term : pivotColumnMatrix pivot column row pivot = column row := by simp [pivotColumnMatrix]
  rw [term]
  have remainder : (∑ j ∈ Finset.univ.erase pivot, pivotColumnMatrix pivot column row j * vector j) =
      if row = pivot then 0 else vector row := by
    by_cases equal : row = pivot
    · subst row
      rw [if_pos rfl]
      apply Finset.sum_eq_zero
      intro j member
      have ne := (Finset.mem_erase.mp member).1
      simp [pivotColumnMatrix, ne, Ne.symm ne]
    · rw [if_neg equal]
      simp only [pivotColumnMatrix, Matrix.updateCol_apply, Matrix.one_apply]
      have reduce : ∀ j ∈ Finset.univ.erase pivot,
          (if j = pivot then column row else if row = j then 1 else 0) * vector j =
            if j = row then vector row else 0 := by
        intro j member
        have ne := (Finset.mem_erase.mp member).1
        by_cases same : j = row
        · subst j; simp [equal]
        · simp [ne, same, Ne.symm same]
      rw [Finset.sum_congr rfl reduce]
      simp [equal]
  rw [remainder]
  split_ifs <;> ring

def pivotResult (system : RationalSystem q) (pivot : Fin q) : RationalSystem q where
  coeff row col := if row = pivot then system.coeff pivot col / system.coeff pivot pivot
    else system.coeff row col - system.coeff row pivot * (system.coeff pivot col / system.coeff pivot pivot)
  rhs row := if row = pivot then system.rhs pivot / system.coeff pivot pivot
    else system.rhs row - system.coeff row pivot * (system.rhs pivot / system.coeff pivot pivot)

theorem augmented_pivotResult (system : RationalSystem q) (pivot row : Fin q) (column : Option (Fin q)) :
    augmented (pivotResult system pivot) row column =
      if row = pivot then augmented system pivot column / system.coeff pivot pivot
      else augmented system row column - system.coeff row pivot * (augmented system pivot column / system.coeff pivot pivot) := by
  cases column <;> rfl

theorem pivotResult_equation (system : RationalSystem q) (pivot : Fin q)
    (nonzero : system.coeff pivot pivot ≠ 0) :
    pivotColumnMatrix pivot (fun row => system.coeff row pivot) * augmented (pivotResult system pivot) =
      augmented system := by
  ext row column
  change (pivotColumnMatrix pivot (fun row => system.coeff row pivot) *ᵥ
    (fun row => augmented (pivotResult system pivot) row column)) row = _
  rw [pivotColumnMatrix_mulVec, augmented_pivotResult, augmented_pivotResult]
  by_cases equal : row = pivot
  · subst row
    simp only [if_true]
    field_simp
  · simp only [equal, if_false, if_true]
    ring

end Counting.GaussianBits
