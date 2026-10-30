import Counting.StackBinarySubtractBits
import Counting.StackBinaryCompareBits

namespace Counting.StackMachine.Binary

/-- A long-division column consumes the next most-significant dividend bit.
Exactly one comparison and at most one subtraction occur in each column. -/
def divisionFlag (bit : Bool) (divisor remainder : List Bool) : Bool :=
  compareBits true divisor (bit::remainder)

def divisionRemainder (bit : Bool) (divisor remainder : List Bool) : List Bool :=
  if divisionFlag bit divisor remainder then (subtractBits false (bit::remainder) divisor).1 else bit::remainder

def divideAcc : List Bool → List Bool → List Bool → List Bool → List Bool × List Bool
  | [], _, remainder, quotient => (quotient,remainder)
  | bit::rest, divisor, remainder, quotient =>
      divideAcc rest divisor (divisionRemainder bit divisor remainder) (divisionFlag bit divisor remainder::quotient)

def divideBits (dividend divisor : List Bool) : List Bool × List Bool :=
  divideAcc dividend.reverse divisor [] []

theorem divisionRemainder_length (bit : Bool) (divisor remainder : List Bool) :
    (divisionRemainder bit divisor remainder).length ≤ max divisor.length (remainder.length+1) := by
  unfold divisionRemainder
  split_ifs
  · rw [subtractBits_length,List.length_cons]
    omega
  · simp only [List.length_cons]
    omega

theorem divideAcc_quotient_length (input divisor remainder quotient : List Bool) :
    (divideAcc input divisor remainder quotient).1.length = input.length+quotient.length := by
  induction input generalizing remainder quotient with
  | nil => simp [divideAcc]
  | cons bit rest ih => rw [divideAcc,ih]; simp only [List.length_cons]; omega

theorem divideAcc_remainder_length (input divisor remainder quotient : List Bool) :
    (divideAcc input divisor remainder quotient).2.length ≤ max divisor.length remainder.length+input.length := by
  induction input generalizing remainder quotient with
  | nil => simp only [divideAcc,List.length_nil,Nat.add_zero]; omega
  | cons bit rest ih =>
      rw [divideAcc]
      have tail := ih (divisionRemainder bit divisor remainder) (divisionFlag bit divisor remainder::quotient)
      have next := divisionRemainder_length bit divisor remainder
      simp only [List.length_cons]
      omega

theorem division_column (bit : Bool) (divisor remainder : List Bool)
    (bounded : Encoding.value remainder < Encoding.value divisor) :
    Encoding.value (divisionRemainder bit divisor remainder) < Encoding.value divisor ∧
      Encoding.value (divisionRemainder bit divisor remainder) + Encoding.value divisor *
          (if divisionFlag bit divisor remainder then 1 else 0) =
        2*Encoding.value remainder+bit.toNat := by
  have compare := compareBits_le divisor (bit::remainder)
  change divisionFlag bit divisor remainder = true ↔ _ at compare
  have grown : Encoding.value (bit::remainder)=2*Encoding.value remainder+bit.toNat := by
    simp only [Encoding.value,Nat.bit_val]
  have small : bit.toNat ≤ 1 := by cases bit <;> decide
  by_cases enough : divisionFlag bit divisor remainder = true
  · have ordered := compare.mp enough
    have difference := subtractBits_of_le false (bit::remainder) divisor (by simpa using ordered)
    simp only [Bool.false_eq_true,ite_false,Nat.add_zero] at difference
    rw [divisionRemainder,if_pos enough,difference]
    simp only [enough,ite_true,Nat.mul_one]
    rw [grown] at ordered ⊢
    omega
  · have smaller : Encoding.value (bit::remainder) < Encoding.value divisor := by
      exact Nat.lt_of_not_ge (fun h => enough (compare.mpr h))
    rw [divisionRemainder,if_neg enough]
    simp only [enough]
    exact ⟨smaller,grown⟩

/-- Numeric interpretation of a stream whose head is most significant. -/
def bigValue : List Bool → Nat
  | [] => 0
  | bit::rest => bit.toNat*2^rest.length+bigValue rest

theorem bigValue_reverse (input : List Bool) : bigValue input.reverse = Encoding.value input := by
  have appendBit (bits : List Bool) (bit : Bool) : bigValue (bits++[bit])=2*bigValue bits+bit.toNat := by
    induction bits with
    | nil => simp [bigValue]
    | cons first rest ih => simp only [List.cons_append,bigValue,List.length_append,List.length_singleton,Nat.pow_succ,ih]; ring
  induction input with
  | nil => rfl
  | cons bit rest ih => rw [List.reverse_cons,appendBit,ih]; simp only [Encoding.value,Nat.bit_val]

/-- Loop invariant for long division: every iteration preserves the
quotient/remainder equation and the strict remainder bound. -/
theorem divideAcc_correct (input divisor remainder quotient : List Bool)
    (bounded : Encoding.value remainder < Encoding.value divisor) :
    Encoding.value (divideAcc input divisor remainder quotient).2 < Encoding.value divisor ∧
      Encoding.value divisor * Encoding.value (divideAcc input divisor remainder quotient).1 +
          Encoding.value (divideAcc input divisor remainder quotient).2 =
        2^input.length*(Encoding.value divisor*Encoding.value quotient+Encoding.value remainder)+bigValue input := by
  induction input generalizing remainder quotient with
  | nil => simpa only [divideAcc,List.length_nil,pow_zero,one_mul,bigValue,Nat.add_zero] using
      And.intro bounded (rfl : Encoding.value divisor*Encoding.value quotient+Encoding.value remainder = _)
  | cons bit rest ih =>
      have column := division_column bit divisor remainder bounded
      have tail := ih (divisionRemainder bit divisor remainder) (divisionFlag bit divisor remainder::quotient) column.1
      rw [divideAcc]
      refine ⟨tail.1,?_⟩
      rw [tail.2]
      simp only [Encoding.value,Nat.bit_val,List.length_cons,Nat.pow_succ,bigValue]
      have flagNat : (divisionFlag bit divisor remainder).toNat =
          (if divisionFlag bit divisor remainder then 1 else 0) := by cases divisionFlag bit divisor remainder <;> rfl
      rw [flagNat]
      have scaled := congrArg (fun value : Nat => 2^rest.length*value) column.2
      nlinarith only [scaled]

theorem divideBits_correct (dividend divisor : List Bool) (positive : 0 < Encoding.value divisor) :
    Encoding.value (divideBits dividend divisor).1 = Encoding.value dividend / Encoding.value divisor ∧
      Encoding.value (divideBits dividend divisor).2 = Encoding.value dividend % Encoding.value divisor := by
  have spec := divideAcc_correct dividend.reverse divisor [] [] (by simpa only [Encoding.value] using positive)
  simp only [Encoding.value,Nat.mul_zero,Nat.add_zero,Nat.zero_add,bigValue_reverse] at spec
  change Encoding.value (divideBits dividend divisor).2 < Encoding.value divisor ∧
    Encoding.value divisor*Encoding.value (divideBits dividend divisor).1+
      Encoding.value (divideBits dividend divisor).2=Encoding.value dividend at spec
  constructor
  · exact (Nat.div_eq_of_lt_le (by nlinarith [spec.2]) (by nlinarith [spec.2])).symm
  · rw [← spec.2]
    simp [Nat.add_mod,Nat.mod_eq_of_lt spec.1]

end Counting.StackMachine.Binary
