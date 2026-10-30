import Counting.StackRationalProduct
import Counting.StackRegisterFrames

namespace Counting.StackMachine.RationalArithmetic.Product
open Routine

set_option maxHeartbeats 200000

theorem normalized_executes (c d numerator denominator sign : List Bool) :
    ∃ time ≤ 1400000*(numerator.length+denominator.length+1)^3,
      Executes normalized (file [] [] c d [] [] numerator denominator sign []) time
        (file (reducedMagnitude (Encoding.value numerator) (Encoding.value denominator)).bits
          (reducedDenominator (Encoding.value numerator) (Encoding.value denominator)).bits
          c d [] [] numerator denominator sign (Nat.gcd (Encoding.value numerator) (Encoding.value denominator)).bits) := by
  obtain ⟨time,bounded,ran⟩ := normalization_executes numerator denominator sign
  have restricted : (file [] [] c d [] [] numerator denominator sign []) ∘ normalizeRoles =
      RationalArithmetic.file numerator denominator [] [] [] sign := by
    funext r; fin_cases r <;> simp [file,RationalArithmetic.file,normalizeRoles]
  refine ⟨time,bounded,?_⟩
  apply relocate_executes_frame normalizationRoutine normalizeRoles _ _ _ _ time restricted _ _ ran
  · intro source; fin_cases source <;> simp [file,RationalArithmetic.file,normalizeRoles]
  · intro r outside
    fin_cases r
    · exact False.elim (outside 3 rfl)
    · exact False.elim (outside 4 rfl)
    · simp [file]
    · simp [file]
    · simp [file]
    · simp [file]
    · simp [file]
    · simp [file]
    · simp [file]
    · exact False.elim (outside 2 rfl)
    · simp [file]
    · simp [file]
    · simp [file]
    · simp [file]
    · simp [file]
    · simp [file]
    · simp [file]
    · simp [file]
    · simp [file]
    · simp [file]

theorem product_executes (a b c d : List Bool) (sa sc : Bool) :
    ∃ time ≤ 2000000*(a.length+b.length+c.length+d.length+1)^3,
      Executes productRoutine (file a b c d [sa] [sc] [] [] [] []) time
        (file (reducedMagnitude (Encoding.value a*Encoding.value c) (Encoding.value b*Encoding.value d)).bits
          (reducedDenominator (Encoding.value a*Encoding.value c) (Encoding.value b*Encoding.value d)).bits
          c d [] [] (Encoding.value a*Encoding.value c).bits (Encoding.value b*Encoding.value d).bits
          [xor sa sc] (Nat.gcd (Encoding.value a*Encoding.value c) (Encoding.value b*Encoding.value d)).bits) := by
  obtain ⟨prepareTime,prepareBound,prepared⟩ := prepare_executes a b c d sa sc
  obtain ⟨normalTime,normalBound,normalRan⟩ := normalized_executes c d
    (Encoding.value a*Encoding.value c).bits (Encoding.value b*Encoding.value d).bits [xor sa sc]
  rw [Encoding.value_bits,Encoding.value_bits] at normalRan
  refine ⟨_,?_,prepared.sequence normalRan⟩
  have aBound := NaturalCall.product_bits_length a c
  have bBound := NaturalCall.product_bits_length b d
  have normPower := Nat.pow_le_pow_left
    (show (Encoding.value a*Encoding.value c).bits.length+(Encoding.value b*Encoding.value d).bits.length+1 ≤
      a.length+b.length+c.length+d.length+1 by omega) 3
  have positive := Nat.one_le_pow' 3 (a.length+b.length+c.length+d.length)
  omega

theorem signed_mul (sa sc : Bool) (a c : Nat) :
    Encoding.signedValue (xor sa sc) (a*c) = Encoding.signedValue sa a*Encoding.signedValue sc c := by
  cases sa <;> cases sc <;> simp [Encoding.signedValue]

/-- The computed raw pair denotes the rational product, even when an
input denominator is zero. Final encoding uses `rational_encode_reduced`. -/
theorem product_spec (sa sc : Bool) (a b c d : Nat) :
    mkRat (Encoding.signedValue (xor sa sc) (a*c)) (b*d) =
      mkRat (Encoding.signedValue sa a) b * mkRat (Encoding.signedValue sc c) d := by
  rw [Rat.mkRat_mul_mkRat,signed_mul]

theorem product_encoding (sa sc : Bool) (a b c d : Nat) :
    Encoding.integer.encode (Encoding.signedValue (xor sa sc) (reducedMagnitude (a*c) (b*d)))++
      Encoding.natural.encode (reducedDenominator (a*c) (b*d)) =
    Encoding.rational.encode (mkRat (Encoding.signedValue sa a) b * mkRat (Encoding.signedValue sc c) d) := by
  rw [← product_spec, rational_encode_reduced]

end Counting.StackMachine.RationalArithmetic.Product
