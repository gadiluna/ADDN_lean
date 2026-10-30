import Counting.StackSignedOutput

namespace Counting.StackMachine.RationalArithmetic
open Signed

/-- The denominator-zero extension agrees with Lean's `mkRat`. -/
def reducedMagnitude (numerator denominator : Nat) : Nat :=
  if denominator=0 then 0 else numerator/Nat.gcd numerator denominator

def reducedDenominator (numerator denominator : Nat) : Nat :=
  if denominator=0 then 1 else denominator/Nat.gcd numerator denominator

theorem reduced_num (sign : Bool) (numerator denominator : Nat) :
    (mkRat (Encoding.signedValue sign numerator) denominator).num =
      Encoding.signedValue sign (reducedMagnitude numerator denominator) := by
  rw [Rat.num_mkRat,signed_natAbs,Nat.gcd_comm denominator numerator]
  by_cases zero : denominator=0
  · simp only [zero,ite_true,reducedMagnitude]
    cases sign <;> rfl
  · simp only [zero,ite_false,reducedMagnitude]
    cases sign
    · rfl
    · change (-(numerator:Int))/(Nat.gcd numerator denominator:Int) = -((numerator/Nat.gcd numerator denominator:Nat):Int)
      rw [Int.neg_ediv_of_dvd (Int.ofNat_dvd.mpr (Nat.gcd_dvd_left numerator denominator))]
      rfl

theorem reduced_den (sign : Bool) (numerator denominator : Nat) :
    (mkRat (Encoding.signedValue sign numerator) denominator).den =
      reducedDenominator numerator denominator := by
  rw [Rat.den_mkRat,signed_natAbs,Nat.gcd_comm denominator numerator]
  rfl

theorem rational_encode_reduced (sign : Bool) (numerator denominator : Nat) :
    Encoding.rational.encode (mkRat (Encoding.signedValue sign numerator) denominator) =
      Encoding.integer.encode (Encoding.signedValue sign (reducedMagnitude numerator denominator))++
        Encoding.natural.encode (reducedDenominator numerator denominator) := by
  rw [Encoding.rational_encode,reduced_num,reduced_den]

theorem reducedMagnitude_size (numerator denominator : Nat) :
    (reducedMagnitude numerator denominator).size ≤ numerator.size := by
  unfold reducedMagnitude
  split_ifs
  · simp
  · exact Nat.size_le_size (Nat.div_le_self _ _)

theorem reducedDenominator_size (numerator denominator : Nat) :
    (reducedDenominator numerator denominator).size ≤ denominator.size+1 := by
  unfold reducedDenominator
  split_ifs
  · simp
  · exact (Nat.size_le_size (Nat.div_le_self _ _)).trans (Nat.le_succ _)

theorem reduced_encoding_length (sign : Bool) (numerator denominator : Nat) :
    (Encoding.rational.encode (mkRat (Encoding.signedValue sign numerator) denominator)).length ≤
      2*(numerator.size+denominator.size)+5 := by
  rw [Encoding.rational_length,reduced_num,reduced_den,signed_natAbs]
  have n := reducedMagnitude_size numerator denominator
  have d := reducedDenominator_size numerator denominator
  omega

end Counting.StackMachine.RationalArithmetic
