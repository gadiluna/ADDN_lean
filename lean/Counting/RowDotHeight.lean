import Counting.GaussianIntermediateArithmetic
import Counting.EncodingRationalRows

namespace Counting.GaussianBits

/-- The larger of the two binary component lengths. Its additive bounds
avoid repeatedly doubling the bound on an accumulated rational sum. -/
def rationalHeight (value : Rat) : Nat := max value.num.natAbs.size value.den.size

theorem rationalHeight_le_encoded (value : Rat) :
    rationalHeight value ≤ (Encoding.rational.encode value).length := by
  rw [Encoding.rational_length]
  unfold rationalHeight
  omega

theorem encoded_le_rationalHeight (value : Rat) :
    (Encoding.rational.encode value).length ≤ 4*rationalHeight value+3 := by
  rw [Encoding.rational_length]
  unfold rationalHeight
  omega

@[simp] theorem rationalHeight_zero : rationalHeight 0=1 := by decide

theorem rationalHeight_mul (first second : Rat) :
    rationalHeight (first*second) ≤ rationalHeight first+rationalHeight second+1 := by
  obtain ⟨num,den⟩ := rational_mul_components first second
  have numerator := (Nat.size_le_size num).trans (nat_product_bits _ _)
  have denominator := (Nat.size_le_size den).trans (nat_product_bits _ _)
  unfold rationalHeight
  apply max_le <;> omega

theorem rationalHeight_add (first second : Rat) :
    rationalHeight (first+second) ≤ rationalHeight first+rationalHeight second+2 := by
  obtain ⟨num,den⟩ := rational_add_components first second
  have numerator := (Nat.size_le_size num).trans (nat_sum_bits _ _)
  have denominator := (Nat.size_le_size den).trans (nat_product_bits _ _)
  have left := nat_product_bits first.num.natAbs second.den
  have right := nat_product_bits second.num.natAbs first.den
  unfold rationalHeight
  apply max_le <;> omega

def dotAcc (pairs : List (Rat×Rat)) (accumulator : Rat) : Rat :=
  pairs.foldl (fun value pair => value+pair.1*pair.2) accumulator

@[simp] theorem dotAcc_nil (accumulator : Rat) : dotAcc [] accumulator=accumulator := rfl
@[simp] theorem dotAcc_cons (pair : Rat×Rat) (pairs : List (Rat×Rat)) (accumulator : Rat) :
    dotAcc (pair::pairs) accumulator=dotAcc pairs (accumulator+pair.1*pair.2) := rfl

theorem dotAcc_height (pairs : List (Rat×Rat)) (accumulator : Rat) :
    rationalHeight (dotAcc pairs accumulator) ≤ rationalHeight accumulator+
      (pairs.map (fun pair => rationalHeight pair.1+rationalHeight pair.2+3)).sum := by
  induction pairs generalizing accumulator with
  | nil => simp
  | cons pair rest ih =>
    have product := rationalHeight_mul pair.1 pair.2
    have added := rationalHeight_add accumulator (pair.1*pair.2)
    have tailBound := ih (accumulator+pair.1*pair.2)
    simp only [dotAcc_cons,List.map_cons,List.sum_cons]
    omega

theorem dotAcc_eq_sum (pairs : List (Rat×Rat)) (accumulator : Rat) :
    dotAcc pairs accumulator=accumulator+(pairs.map (fun pair => pair.1*pair.2)).sum := by
  induction pairs generalizing accumulator with
  | nil => simp
  | cons pair rest ih =>
    simp only [dotAcc_cons,ih,List.map_cons,List.sum_cons]
    ring

/-- A uniform envelope is preserved when a processed pair is removed from
the remaining list and incorporated into the accumulator. -/
def dotEnvelope (pairs : List (Rat×Rat)) (accumulator : Rat) : Nat :=
  rationalHeight accumulator+
    (pairs.map (fun pair => rationalHeight pair.1+rationalHeight pair.2+3)).sum

theorem dotEnvelope_step (pair : Rat×Rat) (pairs : List (Rat×Rat)) (accumulator : Rat) :
    dotEnvelope pairs (accumulator+pair.1*pair.2) ≤ dotEnvelope (pair::pairs) accumulator := by
  have product := rationalHeight_mul pair.1 pair.2
  have added := rationalHeight_add accumulator (pair.1*pair.2)
  simp only [dotEnvelope,List.map_cons,List.sum_cons]
  omega

theorem dotEnvelope_head (pair : Rat×Rat) (pairs : List (Rat×Rat)) (accumulator : Rat) :
    rationalHeight accumulator+rationalHeight pair.1+rationalHeight pair.2+3 ≤
      dotEnvelope (pair::pairs) accumulator := by
  simp only [dotEnvelope,List.map_cons,List.sum_cons]
  omega

end Counting.GaussianBits
