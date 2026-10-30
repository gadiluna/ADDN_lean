import Counting.StackRationalAddOutput
import Counting.StackRationalPairSpec

namespace Counting.StackMachine.RationalArithmetic.Addition
open Routine

def parserRoles : Fin 9 ↪ Fin 22 := ⟨![0,1,2,3,4,5,6,7,8],by decide⟩
abbrev parser : Routine 20 := relocate Pair.parser parserRoles
abbrev completeAddition : Routine 20 := sequence parser (sequence additionRoutine outputRoutine)
def additionFunction (input : List Bool) : List Bool :=
  let sum := rawSum (Pair.firstSign input) (Pair.secondSign input)
    (Encoding.value (Pair.first input).first) (Encoding.value (Pair.first input).second)
    (Encoding.value (Pair.second input).first) (Encoding.value (Pair.second input).second)
  Encoding.rational.encode (mkRat (Signed.value sum.1 sum.2)
    (Encoding.value (Pair.first input).second*Encoding.value (Pair.second input).second))

theorem parser_executes (input : List Bool) :
    ∃ time ≤ 19*input.length+46,
      Executes parser (file input [] [] [] [] [] [] [] [] [] [] []) time
        (file (Pair.first input).first (Pair.first input).second (Pair.second input).first (Pair.second input).second
          [Pair.firstSign input] [Pair.secondSign input] [] [] [] [] [] []) := by
  obtain ⟨time,bounded,ran⟩ := Pair.parser_executes input
  refine ⟨time,bounded,?_⟩
  apply relocate_executes_frame Pair.parser parserRoles _ _ _ _ time _ _ _ ran
  · funext r; fin_cases r <;> simp [file,Pair.file,parserRoles]
  · intro r; fin_cases r <;> simp [file,Pair.file,Pair.result,parserRoles]
  · intro r outside
    fin_cases r
    · exact False.elim (outside 0 rfl)
    · exact False.elim (outside 1 rfl)
    · exact False.elim (outside 2 rfl)
    · exact False.elim (outside 3 rfl)
    · exact False.elim (outside 4 rfl)
    · exact False.elim (outside 5 rfl)
    all_goals simp [file]

theorem addition_computes : ComputesIn completeAddition.program additionFunction (Complexity.polynomial 14000000 3) := by
  intro input
  let a := (Pair.first input).first
  let b := (Pair.first input).second
  let c := (Pair.second input).first
  let d := (Pair.second input).second
  let sa := Pair.firstSign input
  let sc := Pair.secondSign input
  let sum := rawSum sa sc (Encoding.value a) (Encoding.value b) (Encoding.value c) (Encoding.value d)
  let numerator := Encoding.value sum.2
  let denominator := Encoding.value b*Encoding.value d
  let magnitude := reducedMagnitude numerator denominator
  let divisor := reducedDenominator numerator denominator
  obtain ⟨parseTime,parseBound,parsedRun⟩ := parser_executes input
  obtain ⟨coreTime,coreBound,coreRan⟩ := addition_executes a b c d sa sc
  obtain ⟨outputTime,outputBound,outputRan⟩ := output_executes c d sum.2 denominator.bits
    (Nat.gcd numerator denominator).bits magnitude divisor sum.1
  obtain ⟨finish,ran,halted,stored⟩ := parsedRun.sequence (coreRan.sequence outputRan)
  refine ⟨parseTime+1+(coreTime+1+outputTime),finish,?_,⟨?_,halted⟩,?_⟩
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
    change _ ≤ 14000000*(input.length+1)^3
    omega
  · have start : initial completeAddition.program input = ⟨0,file input [] [] [] [] [] [] [] [] [] [] []⟩ := by
      apply congrArg (Config.mk _)
      funext r; fin_cases r <;> simp [file]
    rw [start]
    exact ran
  · rw [stored]
    change Encoding.integer.encode (Encoding.signedValue sum.1 magnitude)++Encoding.natural.encode divisor = _
    exact (rational_encode_reduced sum.1 numerator denominator).symm

theorem additionFunction_rationals (a b : Rat) :
    additionFunction ((Encoding.product Encoding.rational Encoding.rational).encode (a,b)) = Encoding.rational.encode (a+b) := by
  have sum := addition_spec (Encoding.negative a.num) (Encoding.negative b.num)
    a.num.natAbs a.den b.num.natAbs b.den a.den_nz b.den_nz
  simp only [Encoding.signedValue_negative_natAbs,Rat.mkRat_self] at sum
  simp only [additionFunction,Pair.first_rationals,Pair.second_rationals,
    Pair.firstSign_rationals,Pair.secondSign_rationals,Encoding.value_bits]
  rw [sum]

end Counting.StackMachine.RationalArithmetic.Addition
