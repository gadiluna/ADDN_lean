import Mathlib

/-! Arithmetic for binary label lengths. The bounds concern concrete Nat
and rational numerators/denominators, independently of a machine model. -/
namespace Counting.Executable

/-- Signed input coefficients remain integral; subtraction cannot increase
numerator magnitude beyond the sum of the two unsigned labels. -/
theorem rational_difference_labels (a b : Nat) :
    ((a : ℚ) - (b : ℚ)).den = 1 ∧
      ((a : ℚ) - (b : ℚ)).num.natAbs ≤ a+b := by
  have cast : (((a : ℤ) - (b : ℤ) : ℤ) : ℚ) = (a : ℚ) - (b : ℚ) := by norm_cast
  rw [← cast, Rat.den_intCast, Rat.num_intCast]
  exact ⟨rfl, by simpa only [Int.natAbs_natCast] using Int.natAbs_sub_le (a : ℤ) (b : ℤ)⟩

theorem rational_difference_bound (a b M : Nat) (left : a ≤ M) (right : b ≤ M) :
    ((a : ℚ) - (b : ℚ)).den = 1 ∧ ((a : ℚ) - (b : ℚ)).num.natAbs ≤ 2*M := by
  have labels := rational_difference_labels a b
  exact ⟨labels.1, labels.2.trans (by omega)⟩

theorem size_le_of_le_two_pow (a exponent : Nat) (bound : a ≤ 2^exponent) :
    Nat.size a ≤ exponent+1 := by
  simpa only [Nat.size_pow] using Nat.size_le_size bound

theorem twice_size_bound (M : Nat) : Nat.size (2*M) ≤ Nat.size M+1 := by
  apply Nat.size_le.mpr
  have bound := Nat.mul_lt_mul_of_pos_left (Nat.lt_size_self M) (by omega : 0 < 2)
  simpa only [pow_succ, Nat.mul_comm] using bound

/-- Numerator and denominator binary lengths for a flow coefficient. A sign
bit, if encoded separately, contributes at most one additional bit. -/
theorem rational_difference_bits (a b M : Nat) (left : a ≤ M) (right : b ≤ M) :
    Nat.size (((a : ℚ) - (b : ℚ)).num.natAbs) +
      Nat.size (((a : ℚ) - (b : ℚ)).den) ≤ Nat.size M+2 := by
  obtain ⟨den, num⟩ := rational_difference_bound a b M left right
  have size := (Nat.size_le_size num).trans (twice_size_bound M)
  rw [den]
  norm_num only [Nat.size_one]
  omega

/-- The total arc mass under a per-bundle 2^p bound has polynomial binary
length, including the factor n² from all ordered pairs of agents. -/
theorem square_times_power_size (n p : Nat) :
    Nat.size (n^2 * 2^p) ≤ 2 * Nat.size n + p + 1 := by
  have power : n^2 * 2^p ≤ 2^(2 * Nat.size n+p) := by
    have squared := Nat.pow_le_pow_left (Nat.lt_size_self n).le 2
    have scaled := Nat.mul_le_mul_right (2^p) squared
    calc
      _ ≤ (2^Nat.size n)^2 * 2^p := scaled
      _ = _ := by rw [← pow_mul, ← pow_add]; congr 1; omega
  exact size_le_of_le_two_pow _ _ power

theorem square_times_power_size_polynomial (n p : Nat) :
    Nat.size (n^2 * 2^p) ≤ 2*n+p+1 := by
  have bits : Nat.size n ≤ n := Nat.size_le.mpr Nat.lt_two_pow_self
  exact (square_times_power_size n p).trans (by omega)

end Counting.Executable
