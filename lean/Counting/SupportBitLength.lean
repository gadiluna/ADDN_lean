import Counting.SupportBound
import Mathlib.Data.Nat.Size

/-!
# Binary length of the causal-support bound

`Nat.size` is the number of bits in the canonical binary expansion (`0` has
size zero). These arithmetic bounds are independent of any input encoding:
the hypotheses relating depth, visible-node count and label lengths to `L`
must still be established for an explicit encoding.
-/

namespace Counting.SupportBitLength

/-- A base with at most `L` visible nodes and an `L`-bit label fits below
`2^(2L)` (non-strictly). This includes `L=0`. -/
theorem base_le_two_pow (nu M L : Nat) (nodes : nu ≤ L) (label : Nat.size M ≤ L) :
    1 + nu * M ≤ 2 ^ (2 * L) := by
  have hnu : nu < 2 ^ L := nodes.trans_lt Nat.lt_two_pow_self
  have hM : M < 2 ^ L := Nat.size_le.mp label
  have hproduct := Nat.mul_lt_mul_of_lt_of_lt hnu hM
  have hp : (2 : Nat) ^ L * 2 ^ L = 2 ^ (2 * L) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hp] at hproduct
  omega

/-- Exponentiation multiplies the exponent of the binary envelope. -/
theorem support_power_le_two_pow (nu M t L : Nat)
    (nodes : nu ≤ L) (label : Nat.size M ≤ L) :
    (1 + nu * M) ^ t ≤ 2 ^ (2 * L * t) := by
  simpa only [pow_mul] using Nat.pow_le_pow_left (base_le_two_pow nu M L nodes label) t

/-- Precise linear-in-depth binary-size bound for K. -/
theorem support_power_size_le (nu M t L : Nat)
    (nodes : nu ≤ L) (label : Nat.size M ≤ L) :
    Nat.size ((1 + nu * M) ^ t) ≤ 2 * L * t + 1 := by
  have h := Nat.size_le_size (support_power_le_two_pow nu M t L nodes label)
  simpa only [Nat.size_pow] using h

/-- The bounded compatible-order threshold has a size bound linear in depth
and label length, without assuming that either is an actual input length. -/
theorem compatible_order_size_le (nu M t ell L : Nat)
    (nodes : nu ≤ L) (label : Nat.size M ≤ L) (leaders : Nat.size ell ≤ L) :
    Nat.size ((1 + nu * M) ^ t + ell + 2) ≤ 2 * L * t + L + 3 := by
  let E := 2 * L * t + L + 1
  have hK : (1 + nu * M) ^ t ≤ 2 ^ E :=
    (support_power_le_two_pow nu M t L nodes label).trans
      (Nat.pow_le_pow_right (by omega) (by dsimp [E]; omega))
  have hell : ell < 2 ^ E := (Nat.size_le.mp leaders).trans_le
    (Nat.pow_le_pow_right (by omega) (by dsimp [E]; omega))
  have htwo : 2 ≤ (2 : Nat) ^ E := by
    have h := Nat.pow_le_pow_right (n := 2) (by omega) (show 1 ≤ E by dsimp [E]; omega)
    simpa using h
  have hpositive : 0 < (2 : Nat) ^ E := by positivity
  have hsum : (1 + nu * M) ^ t + ell + 2 < 2 ^ (E + 2) := by
    rw [pow_add]
    norm_num
    omega
  have hsize := Nat.size_le.mpr hsum
  simpa [E, Nat.add_assoc] using hsize

/-- If depth, node count and label lengths are bounded by L, K has a
quadratic binary-size bound. -/
theorem support_power_size_polynomial (nu M t L : Nat)
    (depth : t ≤ L) (nodes : nu ≤ L) (label : Nat.size M ≤ L) :
    Nat.size ((1 + nu * M) ^ t) ≤ 2 * (L + 1) ^ 2 + 1 := by
  apply (support_power_size_le nu M t L nodes label).trans
  have hmul := Nat.mul_le_mul_left (2 * L) depth
  nlinarith

/-- Explicit quadratic bound for the two-order theorem's threshold K+ell+2. -/
theorem compatible_order_size_polynomial (nu M t ell L : Nat)
    (depth : t ≤ L) (nodes : nu ≤ L)
    (label : Nat.size M ≤ L) (leaders : Nat.size ell ≤ L) :
    Nat.size ((1 + nu * M) ^ t + ell + 2) ≤ 2 * (L + 1) ^ 2 + 1 := by
  apply (compatible_order_size_le nu M t ell L nodes label leaders).trans
  have hmul := Nat.mul_le_mul_left (2 * L) depth
  nlinarith

/-- A threshold bounded by K+ell+2 inherits the same binary-size guarantee. -/
theorem order_size_polynomial (N nu M t ell L : Nat)
    (orderBound : N ≤ (1 + nu * M) ^ t + ell + 2)
    (depth : t ≤ L) (nodes : nu ≤ L)
    (label : Nat.size M ≤ L) (leaders : Nat.size ell ≤ L) :
    Nat.size N ≤ 2 * (L + 1) ^ 2 + 1 :=
  (Nat.size_le_size orderBound).trans
    (compatible_order_size_polynomial nu M t ell L depth nodes label leaders)

/-- In the paper M already includes the leader count, so bounding its bit
length suffices to bound the length of ell. -/
theorem compatible_order_size_polynomial_of_leaders_le_max (nu M t ell L : Nat)
    (depth : t ≤ L) (nodes : nu ≤ L)
    (label : Nat.size M ≤ L) (leaders : ell ≤ M) :
    Nat.size ((1 + nu * M) ^ t + ell + 2) ≤ 2 * (L + 1) ^ 2 + 1 :=
  compatible_order_size_polynomial nu M t ell L depth nodes label
    ((Nat.size_le_size leaders).trans label)

/-- The same arithmetic guarantee stated as the length of an actual binary list. -/
theorem compatible_order_bits_length_polynomial (nu M t ell L : Nat)
    (depth : t ≤ L) (nodes : nu ≤ L)
    (label : Nat.size M ≤ L) (leaders : Nat.size ell ≤ L) :
    ((1 + nu * M) ^ t + ell + 2).bits.length ≤ 2 * (L + 1) ^ 2 + 1 := by
  simpa only [Nat.size_eq_bits_len] using
    compatible_order_size_polynomial nu M t ell L depth nodes label leaders

/-- Combining the physical support theorem and the arithmetic estimate bounds
the binary length of every causal-support count. The node and label bounds
remain explicit semantic hypotheses, not claims about an unformalized encoding. -/
theorem causal_support_size_polynomial {V : Type} [Fintype V]
    (G : Nat → V → V → Nat) (leader : V → Bool) (t r : Nat)
    (observer : V) (nu M L : Nat) (within : r ≤ t)
    (depth : t ≤ L) (nodeLength : nu ≤ L) (labelLength : Nat.size M ≤ L)
    (nodes : ∀ k, k < t → (visibleNodes G leader k (t - k) observer).card ≤ nu)
    (labels : ∀ k, k < t → ∀ old ∈ visibleNodes G leader k (t - k) observer,
      ∀ new ∈ visibleNodes G leader (k + 1) (t - (k + 1)) observer,
        DirectedCounting.PaperHistory.redMultiplicity G leader k old new ≤ M) :
    Nat.size (causalSupport G r (t - r) observer).card ≤ 2 * (L + 1) ^ 2 + 1 := by
  have hsupport := SupportBound.all_supports_card_le_initial_bound
    G leader t r observer nu M within nodes labels
  exact (Nat.size_le_size hsupport).trans
    (support_power_size_polynomial nu M t L depth nodeLength labelLength)

end Counting.SupportBitLength
