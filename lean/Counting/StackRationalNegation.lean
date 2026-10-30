import Counting.MachineRationalNormalize

namespace Counting.StackMachine.RationalArithmetic
open Routine

abbrev negateSign : Routine 14 := EncodingPrograms.branchRoutine 5 (pushBit 5 false) (pushBit 5 true)

theorem negateSign_executes (numerator denominator : List Bool) (sign : Bool) :
    Executes negateSign (file numerator denominator [] [] [] [sign]) 2
      (file numerator denominator [] [] [] [!sign]) := by
  have reset : Function.update (file numerator denominator [] [] [] [sign]) 5 [] =
      file numerator denominator [] [] [] [] := by
    funext r; fin_cases r <;> simp [file]
  have emitted (bit : Bool) : Executes (pushBit (registers := 14) 5 bit)
      (file numerator denominator [] [] [] []) 1 (file numerator denominator [] [] [] [bit]) := by
    have pushed := pushBit_executes (registers := 14) 5 bit (file numerator denominator [] [] [] [])
    have result : Function.update (file numerator denominator [] [] [] []) 5 [bit] =
        file numerator denominator [] [] [] [bit] := by
      funext r; fin_cases r <;> simp [file]
    change Executes _ _ 1 (Function.update (file numerator denominator [] [] [] []) 5 [bit]) at pushed
    rw [result] at pushed
    exact pushed
  apply Signed.branch_bit 5 (pushBit 5 false) (pushBit 5 true) _ _ sign 1 rfl
  rw [reset]
  cases sign <;> exact emitted _

theorem negation_raw_value (sign : Bool) (numerator denominator : Nat) :
    mkRat (Encoding.signedValue (!sign) numerator) denominator =
      -(mkRat (Encoding.signedValue sign numerator) denominator) := by
  cases sign <;> simp [Encoding.signedValue,Rat.mkRat_eq_div,neg_div]

def negationFunction (input : List Bool) : List Bool :=
  Encoding.rational.encode (mkRat
    (Encoding.signedValue (!(parsedSign input)) (Encoding.value (parsed input).first))
    (Encoding.value (parsed input).second))

abbrev negationRoutine : Routine 14 := sequence rationalParser
  (sequence negateSign (sequence normalizationRoutine formatNormalized))

theorem negation_computes : ComputesIn negationRoutine.program negationFunction
    (Complexity.polynomial 1500000 3) := by
  intro input
  obtain ⟨parseTime,parseBound,parsedRun⟩ := rationalParser_executes input
  let num := (parsed input).first
  let den := (parsed input).second
  let sign := !(parsedSign input)
  let common := Nat.gcd (Encoding.value num) (Encoding.value den)
  let magnitude := reducedMagnitude (Encoding.value num) (Encoding.value den)
  let divisor := reducedDenominator (Encoding.value num) (Encoding.value den)
  have negated := negateSign_executes num den (parsedSign input)
  obtain ⟨normalizeTime,normalizeBound,normalized⟩ := normalization_executes num den [sign]
  obtain ⟨formatTime,formatBound,formatted⟩ := formatNormalized_executes num den common.bits magnitude divisor sign
  obtain ⟨finish,ran,halted,stored⟩ := parsedRun.sequence (negated.sequence (normalized.sequence formatted))
  refine ⟨parseTime+1+(2+1+(normalizeTime+1+formatTime)),finish,?_,⟨?_,halted⟩,?_⟩
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
    change _ ≤ 1500000*(input.length+1)^3
    omega
  · have start : initial negationRoutine.program input = ⟨0,file input [] [] [] [] []⟩ := by
      apply congrArg (Config.mk _)
      funext r; fin_cases r <;> rfl
    rw [start]
    exact ran
  · rw [stored]
    exact (rational_encode_reduced sign (Encoding.value num) (Encoding.value den)).symm

theorem negationFunction_raw (sign : Bool) (numerator denominator : Nat) (suffix : List Bool) :
    negationFunction (sign::(Encoding.natural.encode numerator++Encoding.natural.encode denominator++suffix)) =
      Encoding.rational.encode (-(mkRat (Encoding.signedValue sign numerator) denominator)) := by
  simp only [negationFunction,parsedSign,List.headD_cons,parsed,List.tail_cons,
    Encoding.natural,EncodingPrograms.parsePair_frames,Encoding.value_bits]
  exact congrArg Encoding.rational.encode (negation_raw_value sign numerator denominator)

theorem negationFunction_rational (value : Rat) :
    negationFunction (Encoding.rational.encode value) = Encoding.rational.encode (-value) := by
  rw [Encoding.rational_encode,Encoding.integer_encode,List.cons_append]
  have raw := negationFunction_raw (Encoding.negative value.num) value.num.natAbs value.den []
  simp only [List.append_nil,Encoding.signedValue_negative_natAbs,Rat.mkRat_self] at raw
  exact raw

end Counting.StackMachine.RationalArithmetic
