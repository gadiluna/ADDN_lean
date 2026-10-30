import Counting.StackRationalAddComplete
import Counting.StackRationalNegation

namespace Counting.StackMachine.RationalArithmetic.Addition
open Routine

abbrev negateSecond : Routine 20 := EncodingPrograms.branchRoutine 5 (pushBit 5 false) (pushBit 5 true)
abbrev completeSubtraction : Routine 20 := sequence parser
  (sequence negateSecond (sequence additionRoutine outputRoutine))

def subtractionFunction (input : List Bool) : List Bool :=
  let sum := rawSum (Pair.firstSign input) (!(Pair.secondSign input))
    (Encoding.value (Pair.first input).first) (Encoding.value (Pair.first input).second)
    (Encoding.value (Pair.second input).first) (Encoding.value (Pair.second input).second)
  Encoding.rational.encode (mkRat (Signed.value sum.1 sum.2)
    (Encoding.value (Pair.first input).second*Encoding.value (Pair.second input).second))

theorem negateSecond_executes (a b c d : List Bool) (sa sc : Bool) :
    Executes negateSecond (file a b c d [sa] [sc] [] [] [] [] [] []) 2
      (file a b c d [sa] [!sc] [] [] [] [] [] []) := by
  have reset : Function.update (file a b c d [sa] [sc] [] [] [] [] [] []) 5 [] =
      file a b c d [sa] [] [] [] [] [] [] [] := by
    funext r; fin_cases r <;> simp [file]
  have emitted (bit : Bool) : Executes (pushBit (registers := 20) 5 bit)
      (file a b c d [sa] [] [] [] [] [] [] []) 1 (file a b c d [sa] [bit] [] [] [] [] [] []) := by
    have pushed := pushBit_executes (registers := 20) 5 bit (file a b c d [sa] [] [] [] [] [] [] [])
    have result : Function.update (file a b c d [sa] [] [] [] [] [] [] []) 5 [bit] =
        file a b c d [sa] [bit] [] [] [] [] [] [] := by
      funext r; fin_cases r <;> simp [file]
    change Executes _ _ 1 (Function.update (file a b c d [sa] [] [] [] [] [] [] []) 5 [bit]) at pushed
    rw [result] at pushed
    exact pushed
  apply Signed.branch_bit 5 (pushBit 5 false) (pushBit 5 true) _ _ sc 1 rfl
  rw [reset]
  cases sc <;> exact emitted _

theorem subtraction_computes : ComputesIn completeSubtraction.program subtractionFunction (Complexity.polynomial 15000000 3) := by
  intro input
  let a := (Pair.first input).first
  let b := (Pair.first input).second
  let c := (Pair.second input).first
  let d := (Pair.second input).second
  let sa := Pair.firstSign input
  let sc := !(Pair.secondSign input)
  let sum := rawSum sa sc (Encoding.value a) (Encoding.value b) (Encoding.value c) (Encoding.value d)
  let numerator := Encoding.value sum.2
  let denominator := Encoding.value b*Encoding.value d
  let magnitude := reducedMagnitude numerator denominator
  let divisor := reducedDenominator numerator denominator
  obtain ⟨parseTime,parseBound,parsedRun⟩ := parser_executes input
  have flipped := negateSecond_executes a b c d sa (Pair.secondSign input)
  obtain ⟨coreTime,coreBound,coreRan⟩ := addition_executes a b c d sa sc
  obtain ⟨outputTime,outputBound,outputRan⟩ := output_executes c d sum.2 denominator.bits
    (Nat.gcd numerator denominator).bits magnitude divisor sum.1
  obtain ⟨finish,ran,halted,stored⟩ := parsedRun.sequence (flipped.sequence (coreRan.sequence outputRan))
  refine ⟨parseTime+1+(2+1+(coreTime+1+outputTime)),finish,?_,⟨?_,halted⟩,?_⟩
  · have lengths := Pair.parsed_lengths input
    change a.length+b.length+c.length+d.length+_ ≤ input.length at lengths
    have leftBits := NaturalCall.product_bits_length a d
    have rightBits := NaturalCall.product_bits_length c b
    have sumBits := Signed.addBits_length sa sc (Encoding.value a*Encoding.value d).bits (Encoding.value c*Encoding.value b).bits
    change sum.2.length ≤ _ at sumBits
    have normalizedBits := EncodingPrograms.normalize_length_le sum.2
    rw [Arithmetic.normalize_eq_bits] at normalizedBits
    change numerator.bits.length ≤ sum.2.length at normalizedBits
    have dbits := NaturalCall.product_bits_length b d
    change denominator.bits.length ≤ b.length+d.length at dbits
    have mbits := reducedMagnitude_size numerator denominator
    have vbits := reducedDenominator_size numerator denominator
    rw [← Encoding.bits_length,← Encoding.bits_length] at mbits vbits
    change magnitude.bits.length ≤ numerator.bits.length at mbits
    change divisor.bits.length ≤ denominator.bits.length+1 at vbits
    have power := Nat.pow_le_pow_left (show a.length+b.length+c.length+d.length+1 ≤ input.length+1 by omega) 3
    have linear : input.length+1 ≤ (input.length+1)^3 := by
      have square := Nat.one_le_pow' 2 input.length
      have product := Nat.mul_le_mul_left (input.length+1) square
      nlinarith
    change _ ≤ 15000000*(input.length+1)^3
    omega
  · have start : initial completeSubtraction.program input = ⟨0,file input [] [] [] [] [] [] [] [] [] [] []⟩ := by
      apply congrArg (Config.mk _)
      funext r; fin_cases r <;> simp [file]
    rw [start]
    exact ran
  · rw [stored]
    change Encoding.integer.encode (Encoding.signedValue sum.1 magnitude)++Encoding.natural.encode divisor = _
    exact (rational_encode_reduced sum.1 numerator denominator).symm

theorem subtractionFunction_rationals (a b : Rat) :
    subtractionFunction ((Encoding.product Encoding.rational Encoding.rational).encode (a,b)) = Encoding.rational.encode (a-b) := by
  have sum := addition_spec (Encoding.negative a.num) (!(Encoding.negative b.num))
    a.num.natAbs a.den b.num.natAbs b.den a.den_nz b.den_nz
  rw [negation_raw_value] at sum
  simp only [Encoding.signedValue_negative_natAbs,Rat.mkRat_self] at sum
  simp only [subtractionFunction,Pair.first_rationals,Pair.second_rationals,
    Pair.firstSign_rationals,Pair.secondSign_rationals,Encoding.value_bits]
  rw [sum,sub_eq_add_neg]

end Counting.StackMachine.RationalArithmetic.Addition
