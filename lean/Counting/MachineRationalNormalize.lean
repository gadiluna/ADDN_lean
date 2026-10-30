import Counting.StackRationalMachineOutput
import Counting.StackCompilerComplete

namespace Counting.StackMachine.RationalArithmetic
open Routine

abbrev completeNormalization : Routine 14 := sequence rationalParser
  (sequence normalizationRoutine formatNormalized)

/-- The parser, gcd/divisions, zero-denominator guard, canonical sign and
output framing are all charged. No numeric-size loop is hidden in the bound. -/
theorem normalization_computes : ComputesIn completeNormalization.program
    normalizationFunction (Complexity.polynomial 1500000 3) := by
  intro input
  obtain ⟨parseTime,parseBound,parsedRun⟩ := rationalParser_executes input
  let num := (parsed input).first
  let den := (parsed input).second
  let sign := parsedSign input
  let common := Nat.gcd (Encoding.value num) (Encoding.value den)
  let magnitude := reducedMagnitude (Encoding.value num) (Encoding.value den)
  let divisor := reducedDenominator (Encoding.value num) (Encoding.value den)
  obtain ⟨normalizeTime,normalizeBound,normalized⟩ := normalization_executes num den [sign]
  obtain ⟨formatTime,formatBound,formatted⟩ := formatNormalized_executes num den common.bits magnitude divisor sign
  obtain ⟨finish,ran,halted,stored⟩ := parsedRun.sequence (normalized.sequence formatted)
  refine ⟨parseTime+1+(normalizeTime+1+formatTime),finish,?_,⟨?_,halted⟩,?_⟩
  · have lengths := parsed_lengths input
    change num.length+den.length ≤ input.length at lengths
    have numBits := EncodingPrograms.normalize_length_le num
    have denBits := EncodingPrograms.normalize_length_le den
    rw [Arithmetic.normalize_eq_bits,Encoding.bits_length] at numBits denBits
    have magnitudeSize := reducedMagnitude_size (Encoding.value num) (Encoding.value den)
    have divisorSize := reducedDenominator_size (Encoding.value num) (Encoding.value den)
    change magnitude.size ≤ (Encoding.value num).size at magnitudeSize
    change divisor.size ≤ (Encoding.value den).size+1 at divisorSize
    rw [Encoding.bits_length,Encoding.bits_length] at formatBound
    have normalizedBound := Nat.pow_le_pow_left
      (show num.length+den.length+1 ≤ input.length+1 by omega) 3
    have linear : input.length+1 ≤ (input.length+1)^3 := by
      have square := Nat.one_le_pow' 2 input.length
      have product := Nat.mul_le_mul_left (input.length+1) square
      nlinarith
    change parseTime+1+(normalizeTime+1+formatTime) ≤ 1500000*(input.length+1)^3
    omega
  · have start : initial completeNormalization.program input =
        ⟨0,file input [] [] [] [] []⟩ := by
      apply congrArg (Config.mk _)
      funext r; fin_cases r <;> rfl
    rw [start]
    exact ran
  · rw [stored]
    change Encoding.integer.encode (Encoding.signedValue sign magnitude)++Encoding.natural.encode divisor = _
    exact (rational_encode_reduced sign (Encoding.value num) (Encoding.value den)).symm

end Counting.StackMachine.RationalArithmetic

namespace Counting.Machine
open StackMachine.RationalArithmetic

def rationalNormalizationProgram : Program := StackMachine.Compiler.compile completeNormalization.program

theorem rationalNormalization_computesCleanIn : Complexity.ComputesCleanIn rationalNormalizationProgram
    normalizationFunction (Complexity.polynomial (20*(1500000+14+5)^2) 6) := by
  have compiled := StackMachine.Compiler.computesCleanIn normalization_computes
  intro input
  obtain ⟨time,output,bounded,halted,tape⟩ := compiled input
  refine ⟨time,output,bounded.trans ?_,halted,tape⟩
  change 20*(input.length+14+1500000*(input.length+1)^3+4)^2 ≤
    (20*(1500000+14+5)^2)*(input.length+1)^6
  have linear : input.length+1 ≤ (input.length+1)^3 := by
    have square := Nat.one_le_pow' 2 input.length
    have product := Nat.mul_le_mul_left (input.length+1) square
    nlinarith
  have positive := Nat.one_le_pow' 3 input.length
  have base : input.length+14+1500000*(input.length+1)^3+4 ≤
      (1500000+14+5)*(input.length+1)^3 := by omega
  calc
    _ ≤ 20*((1500000+14+5)*(input.length+1)^3)^2 :=
      Nat.mul_le_mul_left 20 (Nat.pow_le_pow_left base 2)
    _ = _ := by ring

/-- Every canonical rational encoding is reproduced with the entire output
tape clean, including work cells outside the encoded result. -/
theorem rationalNormalization_rational_clean (value : Rat) :
    ∃ time output,
      time ≤ (20*(1500000+14+5)^2)*(2*(value.num.natAbs.size+value.den.size)+4)^6 ∧
      HaltsAt rationalNormalizationProgram (Encoding.rational.encode value) time output ∧
      output.tape.denotes = Turing.Tape.mk₁ ((Encoding.rational.encode value).map bitSymbol) := by
  obtain ⟨time,output,bounded,halted,tape⟩ := rationalNormalization_computesCleanIn (Encoding.rational.encode value)
  refine ⟨time,output,?_,halted,?_⟩
  · simpa only [Complexity.polynomial,Encoding.rational_length,Nat.add_assoc] using bounded
  · rw [normalizationFunction_rational] at tape
    exact tape

/-- Unreduced signed numerator/denominator inputs are normalized to the
existing rational codec, including negative zero and denominator zero. -/
theorem rationalNormalization_raw_clean (sign : Bool) (numerator denominator : Nat) (suffix : List Bool) :
    ∃ time output,
      time ≤ (20*(1500000+14+5)^2)*(2*numerator.size+2*denominator.size+suffix.length+4)^6 ∧
      HaltsAt rationalNormalizationProgram
        (sign::(Encoding.natural.encode numerator++Encoding.natural.encode denominator++suffix)) time output ∧
      output.tape.denotes = Turing.Tape.mk₁
        ((Encoding.rational.encode (mkRat (Encoding.signedValue sign numerator) denominator)).map bitSymbol) := by
  obtain ⟨time,output,bounded,halted,tape⟩ := rationalNormalization_computesCleanIn
    (sign::(Encoding.natural.encode numerator++Encoding.natural.encode denominator++suffix))
  refine ⟨time,output,?_,halted,?_⟩
  · simpa only [Complexity.polynomial,List.length_cons,List.length_append,Encoding.natural_length,
      show 2*numerator.size+1+(2*denominator.size+1)+suffix.length+1+1 =
        2*numerator.size+2*denominator.size+suffix.length+4 by omega] using bounded
  · rw [normalizationFunction_raw] at tape
    exact tape

end Counting.Machine
