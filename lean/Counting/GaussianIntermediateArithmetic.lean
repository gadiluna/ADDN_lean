import Counting.GaussianIntermediateActual

/-! Bounds for the temporary rational products and unreduced integer
cross-products used by row arithmetic. These bounds supplement the much
sharper determinant bound for stored entries; they are not step-cost
claims for an arithmetic implementation. -/
namespace Counting.GaussianBits

theorem nat_product_bits (a b : Nat) : (a*b).size ≤ a.size+b.size+1 := by
  have envelope : a*b ≤ 2^(a.size+b.size) := by
    rw [pow_add]
    exact Nat.mul_le_mul (Nat.lt_size_self a).le (Nat.lt_size_self b).le
  simpa only [Nat.size_pow] using Nat.size_le_size envelope

theorem nat_sum_bits (a b : Nat) : (a+b).size ≤ max a.size b.size+1 := by
  apply Nat.size_le.mpr
  have first : a < 2^(max a.size b.size) :=
    (Nat.lt_size_self a).trans_le (Nat.pow_le_pow_right (by decide) (le_max_left _ _))
  have second : b < 2^(max a.size b.size) :=
    (Nat.lt_size_self b).trans_le (Nat.pow_le_pow_right (by decide) (le_max_right _ _))
  rw [pow_succ]
  omega

theorem rational_mul_components (a b : ℚ) :
    (a*b).num.natAbs ≤ a.num.natAbs*b.num.natAbs ∧ (a*b).den ≤ a.den*b.den := by
  have nonzero : (a.den : ℤ) * b.den ≠ 0 := mul_ne_zero (by exact_mod_cast a.den_ne_zero) (by exact_mod_cast b.den_ne_zero)
  have fraction : a*b = (((a.num*b.num : ℤ) : ℚ) / ((a.den : ℤ)*b.den : ℤ)) := by
    push_cast
    rw [mul_div_mul_comm, Rat.num_div_den, Rat.num_div_den]
  have bounded := fraction_components (a.num*b.num) ((a.den : ℤ)*b.den) nonzero
  rw [← fraction] at bounded
  simpa only [Int.natAbs_mul, Int.natAbs_natCast] using bounded

theorem rationalBits_mul (a b : ℚ) : rationalBits (a*b) ≤ rationalBits a+rationalBits b+2 := by
  obtain ⟨num, den⟩ := rational_mul_components a b
  have numerator := (Nat.size_le_size num).trans (nat_product_bits _ _)
  have denominator := (Nat.size_le_size den).trans (nat_product_bits _ _)
  unfold rationalBits
  omega

theorem rational_add_components (a b : ℚ) :
    (a+b).num.natAbs ≤ a.num.natAbs*b.den+b.num.natAbs*a.den ∧ (a+b).den ≤ a.den*b.den := by
  have nonzero : (a.den : ℤ) * b.den ≠ 0 := mul_ne_zero (by exact_mod_cast a.den_ne_zero) (by exact_mod_cast b.den_ne_zero)
  have fraction : a+b = (((a.num*b.den+b.num*a.den : ℤ) : ℚ) / ((a.den : ℤ)*b.den : ℤ)) := by
    push_cast
    rw [add_div, mul_div_mul_right _ _ (by exact_mod_cast b.den_ne_zero),
      mul_comm (a.den : ℚ), mul_div_mul_right _ _ (by exact_mod_cast a.den_ne_zero),
      Rat.num_div_den, Rat.num_div_den]
  have bounded := fraction_components (a.num*b.den+b.num*a.den) ((a.den : ℤ)*b.den) nonzero
  rw [← fraction] at bounded
  have sumBound := Int.natAbs_add_le (a.num*b.den) (b.num*a.den)
  simp only [Int.natAbs_mul, Int.natAbs_natCast] at sumBound bounded
  exact ⟨bounded.1.trans sumBound, bounded.2⟩

theorem rationalBits_add (a b : ℚ) : rationalBits (a+b) ≤ 2*(rationalBits a+rationalBits b)+3 := by
  obtain ⟨num, den⟩ := rational_add_components a b
  have first := nat_product_bits a.num.natAbs b.den
  have second := nat_product_bits b.num.natAbs a.den
  have numerator := (Nat.size_le_size num).trans (nat_sum_bits _ _)
  have denominator := (Nat.size_le_size den).trans (nat_product_bits _ _)
  have maxBound : max (a.num.natAbs*b.den).size (b.num.natAbs*a.den).size ≤ rationalBits a+rationalBits b+1 := by
    apply max_le <;> unfold rationalBits <;> omega
  unfold rationalBits at *
  omega

/-- The row-add expression `old + factor*source` remains polynomial even
before its final result is reduced and stored. -/
theorem row_add_temporary_bits (old factor source : ℚ) (bound : Nat)
    (oldBound : rationalBits old ≤ bound) (factorBound : rationalBits factor ≤ bound)
    (sourceBound : rationalBits source ≤ bound) :
    rationalBits (factor*source) ≤ 2*bound+2 ∧
      rationalBits (old+factor*source) ≤ 6*bound+7 := by
  have product := rationalBits_mul factor source
  have total := rationalBits_add old (factor*source)
  omega

/-- Integer operands of fraction multiplication, before gcd reduction. -/
theorem raw_product_bits (a b : ℚ) (bound : Nat)
    (left : rationalBits a ≤ bound) (right : rationalBits b ≤ bound) :
    (a.num*b.num).natAbs.size ≤ 2*bound+1 ∧ (a.den*b.den).size ≤ 2*bound+1 := by
  rw [Int.natAbs_mul]
  have numerator := nat_product_bits a.num.natAbs b.num.natAbs
  have denominator := nat_product_bits a.den b.den
  unfold rationalBits at *
  omega

/-- Integer cross-products and their sum, before fraction-addition gcd
reduction; signed cancellation can only decrease their absolute value. -/
theorem raw_addition_bits (a b : ℚ) (bound : Nat)
    (left : rationalBits a ≤ bound) (right : rationalBits b ≤ bound) :
    (a.num*b.den+b.num*a.den : ℤ).natAbs.size ≤ 2*bound+2 ∧
      (a.den*b.den).size ≤ 2*bound+1 := by
  have first := nat_product_bits a.num.natAbs b.den
  have second := nat_product_bits b.num.natAbs a.den
  have sumBound := Int.natAbs_add_le (a.num*b.den) (b.num*a.den)
  simp only [Int.natAbs_mul, Int.natAbs_natCast] at sumBound
  have numerator := (Nat.size_le_size sumBound).trans (nat_sum_bits _ _)
  have denominator := nat_product_bits a.den b.den
  have maxBound : max (a.num.natAbs*b.den).size (b.num.natAbs*a.den).size ≤ 2*bound+1 := by
    apply max_le <;> unfold rationalBits at * <;> omega
  unfold rationalBits at *
  omega

end Counting.GaussianBits
