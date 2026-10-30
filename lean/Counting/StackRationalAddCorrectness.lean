import Counting.StackRationalAddSum

namespace Counting.StackMachine.RationalArithmetic.Addition
open Routine

def normalizeRoles : Fin 16 ↪ Fin 22 := ⟨![9,8,11,0,1,10,12,13,14,15,16,17,18,19,20,21],by decide⟩
abbrev normalized : Routine 20 := relocate normalizationRoutine normalizeRoles
abbrev additionRoutine : Routine 20 := sequence prepare normalized

theorem normalized_executes (c d numerator denominator sign : List Bool) :
    ∃ time ≤ 1400000*(numerator.length+denominator.length+1)^3,
      Executes normalized (file [] [] c d [] [] [] [] denominator numerator sign []) time
        (file (reducedMagnitude (Encoding.value numerator) (Encoding.value denominator)).bits
          (reducedDenominator (Encoding.value numerator) (Encoding.value denominator)).bits
          c d [] [] [] [] denominator numerator sign (Nat.gcd (Encoding.value numerator) (Encoding.value denominator)).bits) := by
  obtain ⟨time,bounded,ran⟩ := normalization_executes numerator denominator sign
  have restricted : (file [] [] c d [] [] [] [] denominator numerator sign []) ∘ normalizeRoles =
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

theorem addition_executes (a b c d : List Bool) (sa sc : Bool) :
    ∃ time ≤ 13000000*(a.length+b.length+c.length+d.length+1)^3,
      Executes additionRoutine (file a b c d [sa] [sc] [] [] [] [] [] []) time
        (file
          (reducedMagnitude (Encoding.value (rawSum sa sc (Encoding.value a) (Encoding.value b) (Encoding.value c) (Encoding.value d)).2)
            (Encoding.value b*Encoding.value d)).bits
          (reducedDenominator (Encoding.value (rawSum sa sc (Encoding.value a) (Encoding.value b) (Encoding.value c) (Encoding.value d)).2)
            (Encoding.value b*Encoding.value d)).bits
          c d [] [] [] [] (Encoding.value b*Encoding.value d).bits
          (rawSum sa sc (Encoding.value a) (Encoding.value b) (Encoding.value c) (Encoding.value d)).2
          [(rawSum sa sc (Encoding.value a) (Encoding.value b) (Encoding.value c) (Encoding.value d)).1]
          (Nat.gcd (Encoding.value (rawSum sa sc (Encoding.value a) (Encoding.value b) (Encoding.value c) (Encoding.value d)).2)
            (Encoding.value b*Encoding.value d)).bits) := by
  let sum := rawSum sa sc (Encoding.value a) (Encoding.value b) (Encoding.value c) (Encoding.value d)
  obtain ⟨prepareTime,prepareBound,prepared⟩ := prepare_executes a b c d sa sc
  obtain ⟨normalTime,normalBound,normalRan⟩ := normalized_executes c d sum.2
    (Encoding.value b*Encoding.value d).bits [sum.1]
  rw [Encoding.value_bits] at normalRan
  refine ⟨_,?_,prepared.sequence normalRan⟩
  have left := NaturalCall.product_bits_length a d
  have right := NaturalCall.product_bits_length c b
  have denominator := NaturalCall.product_bits_length b d
  have sumBound := Signed.addBits_length sa sc (Encoding.value a*Encoding.value d).bits (Encoding.value c*Encoding.value b).bits
  change sum.2.length ≤ _ at sumBound
  have power := Nat.pow_le_pow_left
    (show sum.2.length+(Encoding.value b*Encoding.value d).bits.length+1 ≤
      2*(a.length+b.length+c.length+d.length+1) by omega) 3
  have positive := Nat.one_le_pow' 3 (a.length+b.length+c.length+d.length)
  nlinarith

theorem rawSum_value (sa sc : Bool) (a b c d : Nat) :
    Signed.value (rawSum sa sc a b c d).1 (rawSum sa sc a b c d).2 =
      Encoding.signedValue sa a*(d:Int)+Encoding.signedValue sc c*(b:Int) := by
  have sum := Signed.addBits_value sa sc (a*d).bits (c*b).bits
  change Signed.value (rawSum sa sc a b c d).1 (rawSum sa sc a b c d).2 = _ at sum
  rw [sum]
  simp only [Signed.value,Encoding.value_bits]
  cases sa <;> cases sc <;> simp [Encoding.signedValue]

/-- On the canonical rational domain both denominators are nonzero. The
finite program itself remains bounded on every raw input. -/
theorem addition_spec (sa sc : Bool) (a b c d : Nat) (bpos : b ≠ 0) (dpos : d ≠ 0) :
    mkRat (Signed.value (rawSum sa sc a b c d).1 (rawSum sa sc a b c d).2) (b*d) =
      mkRat (Encoding.signedValue sa a) b + mkRat (Encoding.signedValue sc c) d := by
  rw [Rat.mkRat_add_mkRat _ _ bpos dpos,rawSum_value]

theorem addition_encoding (sa sc : Bool) (a b c d : Nat) (bpos : b ≠ 0) (dpos : d ≠ 0) :
    Encoding.integer.encode (Encoding.signedValue (rawSum sa sc a b c d).1
      (reducedMagnitude (Encoding.value (rawSum sa sc a b c d).2) (b*d)))++
      Encoding.natural.encode (reducedDenominator (Encoding.value (rawSum sa sc a b c d).2) (b*d)) =
    Encoding.rational.encode (mkRat (Encoding.signedValue sa a) b + mkRat (Encoding.signedValue sc c) d) := by
  rw [← addition_spec sa sc a b c d bpos dpos]
  exact (rational_encode_reduced _ _ _).symm

end Counting.StackMachine.RationalArithmetic.Addition
