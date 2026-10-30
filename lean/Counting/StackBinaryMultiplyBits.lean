import Counting.StackBinaryAdd

namespace Counting.StackMachine.Binary
open Arithmetic

/-- Schoolbook multiplication processes each multiplier bit once, shifts
by one place, and adds only when the processed bit is set. -/
def multiplyAcc : List Bool → List Bool → List Bool → List Bool
  | [], _, accumulator => accumulator
  | bit::rest, shifted, accumulator =>
      multiplyAcc rest (false::shifted) (if bit then addBits false accumulator shifted else accumulator)

theorem multiplyAcc_value (multiplier shifted accumulator : List Bool) :
    Encoding.value (multiplyAcc multiplier shifted accumulator) =
      Encoding.value accumulator + Encoding.value multiplier * Encoding.value shifted := by
  induction multiplier generalizing shifted accumulator with
  | nil => simp [multiplyAcc, Encoding.value]
  | cons bit rest ih =>
      rw [multiplyAcc, ih]
      cases bit <;>
        simp only [Bool.false_eq_true, if_false, if_true, Encoding.value, Nat.bit_val,
          Bool.toNat_false, Bool.toNat_true, addBits_value]
      all_goals ring

/-- Even a deliberately loose length estimate stays polynomial in the
operand bit lengths; no estimate depends on the represented integer value. -/
theorem multiplyAcc_length (multiplier shifted accumulator : List Bool) :
    (multiplyAcc multiplier shifted accumulator).length ≤
      accumulator.length + multiplier.length*(shifted.length+multiplier.length+1) := by
  induction multiplier generalizing shifted accumulator with
  | nil => simp [multiplyAcc]
  | cons bit rest ih =>
      rw [multiplyAcc]
      have bound := ih (false::shifted) (if bit then addBits false accumulator shifted else accumulator)
      have added : (if bit then addBits false accumulator shifted else accumulator).length ≤
          accumulator.length+shifted.length+1 := by
        cases bit
        · simp only [Bool.false_eq_true, if_false]; omega
        · exact addBits_length false accumulator shifted
      simp only [List.length_cons] at bound ⊢
      nlinarith

def multiplyBits (first second : List Bool) : List Bool := multiplyAcc second first []

theorem multiplyBits_value (first second : List Bool) :
    Encoding.value (multiplyBits first second) = Encoding.value first*Encoding.value second := by
  rw [multiplyBits, multiplyAcc_value, Encoding.value, Nat.zero_add, Nat.mul_comm]

theorem multiplyBits_length (first second : List Bool) :
    (multiplyBits first second).length ≤ second.length*(first.length+second.length+1) := by
  simpa only [multiplyBits, List.length_nil, Nat.zero_add] using multiplyAcc_length second first []

theorem multiplyBits_natural (first second : Nat) :
    normalize (multiplyBits first.bits second.bits) = (first*second).bits := by
  rw [normalize_eq_bits, multiplyBits_value, Encoding.value_bits, Encoding.value_bits]

end Counting.StackMachine.Binary
