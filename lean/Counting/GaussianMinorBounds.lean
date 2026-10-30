import Mathlib

/-! Integer-minor bounds for exact Gaussian bit complexity. These estimates
support the actual-intermediate bounds in GaussianIntermediateActual and
GaussianIntermediateRun. MachineGaussianPolynomial supplies the physical
running-time theorem for the solver. -/
namespace Counting.GaussianBits
open scoped BigOperators

/-- An elementary Leibniz bound, valid also for the empty matrix. -/
theorem determinant_natAbs_le (n M : Nat) (A : Matrix (Fin n) (Fin n) ℤ)
    (entries : ∀ i j, (A i j).natAbs ≤ M) : A.det.natAbs ≤ n.factorial * M^n := by
  rw [Matrix.det_apply]
  apply (Int.natAbs_sum_le _ _).trans
  calc
    _ ≤ ∑ _σ : Equiv.Perm (Fin n), M^n := by
      apply Finset.sum_le_sum
      intro σ _
      simp only [Units.smul_def, smul_eq_mul, Int.natAbs_mul, Int.units_natAbs, one_mul]
      change Int.natAbsHom (∏ i, A (σ i) i) ≤ _
      rw [map_prod]
      calc
        _ ≤ ∏ _i : Fin n, M := Finset.prod_le_prod (fun _ _ => Nat.zero_le _) (fun i _ => entries (σ i) i)
        _ = _ := by simp
    _ = n.factorial * M^n := by simp [Fintype.card_perm]

/-- The binary length of n! M^n is polynomial in n and size(M). -/
theorem determinant_envelope_bits (n M : Nat) :
    (n.factorial * M^n).size ≤ n * (n.size + M.size) + 1 := by
  have envelope : n.factorial * M^n ≤ 2^(n * (n.size+M.size)) := by
    calc
      _ ≤ n^n * M^n := Nat.mul_le_mul_right _ (Nat.factorial_le_pow n)
      _ = (n*M)^n := (mul_pow n M n).symm
      _ ≤ (2^n.size * 2^M.size)^n :=
        Nat.pow_le_pow_left (Nat.mul_le_mul (Nat.lt_size_self n).le (Nat.lt_size_self M).le) n
      _ = _ := by rw [← pow_add, ← pow_mul]; congr 1; ring
  simpa only [Nat.size_pow] using Nat.size_le_size envelope

theorem determinant_bits (n M : Nat) (A : Matrix (Fin n) (Fin n) ℤ)
    (entries : ∀ i j, (A i j).natAbs ≤ M) :
    A.det.natAbs.size ≤ n * (n.size + M.size) + 1 :=
  (Nat.size_le_size (determinant_natAbs_le n M A entries)).trans (determinant_envelope_bits n M)

/-- Reduction of an integer fraction cannot increase either magnitude. -/
theorem fraction_components (a b : ℤ) (nonzero : b ≠ 0) :
    ((a : ℚ) / b).num.natAbs ≤ a.natAbs ∧ ((a : ℚ) / b).den ≤ b.natAbs := by
  obtain ⟨c, numerator, denominator⟩ := Rat.exists_eq_mul_div_num_and_eq_mul_div_den a nonzero
  have cne : c ≠ 0 := by
    intro zero
    rw [zero, zero_mul] at denominator
    exact nonzero denominator
  have positive := Int.natAbs_pos.mpr cne
  have num := congrArg Int.natAbs numerator
  have den := congrArg Int.natAbs denominator
  simp only [Int.natAbs_mul, Int.natAbs_natCast] at num den
  constructor
  · rw [num]
    exact Nat.le_mul_of_pos_left _ positive
  · rw [den]
    exact Nat.le_mul_of_pos_left _ positive

/-- Any quotient of two bounded integer minors has polynomial numerator
and denominator lengths. Applying this to a Gaussian run still requires
proving its minor representation invariant. -/
theorem minor_quotient_bits (n M : Nat) (A B : Matrix (Fin n) (Fin n) ℤ)
    (left : ∀ i j, (A i j).natAbs ≤ M) (right : ∀ i j, (B i j).natAbs ≤ M)
    (denominator : B.det ≠ 0) :
    ((A.det : ℚ) / B.det).num.natAbs.size + ((A.det : ℚ) / B.det).den.size ≤
      2 * (n * (n.size + M.size) + 1) := by
  obtain ⟨num, den⟩ := fraction_components A.det B.det denominator
  have numeratorBits := (Nat.size_le_size num).trans (determinant_bits n M A left)
  have denominatorBits := (Nat.size_le_size den).trans (determinant_bits n M B right)
  omega

end Counting.GaussianBits
