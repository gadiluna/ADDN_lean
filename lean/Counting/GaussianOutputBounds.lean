import Counting.GaussianInputBounds

/-! Polynomial binary lengths of every returned solution of the actual
rectangular solver. This does not by itself bound intermediate arithmetic. -/
namespace Counting.GaussianBits
open Counting.Executable
open DirectedCounting.GaussianGeneratorCompleteness
open scoped BigOperators Matrix

theorem integer_solution_quotient (n : Nat) (A : Matrix (Fin n) (Fin n) ℤ)
    (b : Fin n → ℤ) (x : Fin n → ℚ) (nonzero : A.det ≠ 0)
    (solves : A.map (Int.cast : ℤ → ℚ) *ᵥ x = fun i => (b i : ℚ)) (i : Fin n) :
    x i = ((A.updateCol i b).det : ℚ) / (A.det : ℚ) := by
  let AQ := A.map (Int.cast : ℤ → ℚ)
  have transformed := congrArg (fun v => AQ.adjugate *ᵥ v) solves
  change AQ.adjugate *ᵥ (AQ *ᵥ x) = AQ.adjugate *ᵥ (fun j => (b j : ℚ)) at transformed
  rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec,
    Matrix.one_mulVec, ← Matrix.cramer_eq_adjugate_mulVec] at transformed
  have component := congrFun transformed i
  simp only [Pi.smul_apply, smul_eq_mul, Matrix.cramer_apply] at component
  have updated : AQ.updateCol i (fun j => (b j : ℚ)) =
      (A.updateCol i b).map (Int.cast : ℤ → ℚ) := by
    ext r c
    simp [AQ, Matrix.updateCol_apply]
  rw [updated, ← Int.cast_det (A.updateCol i b)] at component
  change (A.map (Int.cast : ℤ → ℚ)).det * x i = _ at component
  rw [← Int.cast_det A] at component
  apply (eq_div_iff (by exact_mod_cast nonzero : (A.det : ℚ) ≠ 0)).mpr
  simpa only [mul_comm] using component

theorem integer_solution_bits (n M : Nat) (A : Matrix (Fin n) (Fin n) ℤ)
    (b : Fin n → ℤ) (x : Fin n → ℚ) (nonzero : A.det ≠ 0)
    (solves : A.map (Int.cast : ℤ → ℚ) *ᵥ x = fun i => (b i : ℚ))
    (coeffBound : ∀ i j, (A i j).natAbs ≤ M)
    (rhsBound : ∀ i, (b i).natAbs ≤ M) (i : Fin n) :
    (x i).num.natAbs.size + (x i).den.size ≤ 2*(n*(n.size+M.size)+1) := by
  rw [integer_solution_quotient n A b x nonzero solves i]
  apply minor_quotient_bits n M (A.updateCol i b) A _ coeffBound nonzero
  intro r c
  by_cases same : c = i
  · subst c
    simpa only [Matrix.updateCol_self] using rhsBound r
  · simpa only [Matrix.updateCol_ne same] using coeffBound r c

/-- The actual accepted square system has nonzero determinant; no full-rank
assumption is added to the public solver interface. -/
theorem accepted_normal_det_ne_zero (width : Nat) (rows : List Equation)
    (result : Array ℚ) (accepted : solveLinear? width rows = some result) :
    (normalSystem width rows).coeff.det ≠ 0 := by
  obtain ⟨_, _, satisfies⟩ := solveLinear_sound width rows result accepted
  have injective := rowMatrix_injective_of_unique width rows (arrayVector width result) satisfies
    (fun y hy => solveLinear_unique width rows result accepted y hy)
  have gram : Function.Injective (normalSystem width rows).coeff.mulVec := by
    rw [normalSystem_coeff]
    exact (gram_injective_iff _).mpr injective
  exact ((Matrix.isUnit_iff_isUnit_det _).mp (Matrix.mulVec_injective_iff_isUnit.mp gram)).ne_zero

/-- Every rational returned by solveLinear? has polynomial numerator and
denominator lengths in the actual integral rectangular input bounds. -/
theorem solveLinear_output_bits (width : Nat) (rows : List Equation) (M : Nat)
    (result : Array ℚ) (accepted : solveLinear? width rows = some result)
    (coeff : ∀ r i, (rowMatrix width rows r i).den = 1 ∧
      (rowMatrix width rows r i).num.natAbs ≤ M)
    (rhs : ∀ r, (rowRhs rows r).den = 1 ∧ (rowRhs rows r).num.natAbs ≤ M)
    (i : Fin width) :
    (arrayVector width result i).num.natAbs.size + (arrayVector width result i).den.size ≤
      2 * (width * (width.size + rows.length.size + 2*M.size + 1) + 1) := by
  have coefficient := normal_coeff_cast width rows (fun r i => (coeff r i).1)
  have vector := normal_rhs_cast width rows (fun r i => (coeff r i).1) (fun r => (rhs r).1)
  have nonzero := accepted_normal_det_ne_zero width rows result accepted
  rw [coefficient, ← Int.cast_det] at nonzero
  have nonzeroInt : (integerNormalCoeff width rows).det ≠ 0 := by exact_mod_cast nonzero
  obtain ⟨_, _, original⟩ := solveLinear_sound width rows result accepted
  have solves := normal_satisfies width rows (arrayVector width result) original
  change (normalSystem width rows).coeff *ᵥ _ = (normalSystem width rows).rhs at solves
  rw [coefficient, vector] at solves
  obtain ⟨left, right⟩ := integer_normal_bounds width rows M
    (fun r i => (coeff r i).2) (fun r => (rhs r).2)
  have bounded := integer_solution_bits width (rows.length*M^2)
    (integerNormalCoeff width rows) (integerNormalRhs width rows) (arrayVector width result)
    nonzeroInt solves left right i
  have envelope := normal_envelope_bits rows.length M
  apply bounded.trans
  apply Nat.mul_le_mul_left 2
  apply Nat.add_le_add_right
  apply Nat.mul_le_mul_left width
  omega

end Counting.GaussianBits
