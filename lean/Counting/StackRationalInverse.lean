import Counting.MachineRationalNormalize

namespace Counting.StackMachine.RationalArithmetic
open Routine

abbrev swapOperands : Routine 14 := sequence (move 13 0 6 7)
  (sequence (move 13 1 0 7) (move 13 6 1 7))

theorem swapOperands_executes (numerator denominator sign : List Bool) :
    Executes swapOperands (file numerator denominator [] [] [] sign)
      (12*numerator.length+6*denominator.length+14)
      (file denominator numerator [] [] [] sign) := by
  let middle : Fin 16 → List Bool := ![[],denominator,[],[],[],sign,numerator,[],[],[],[],[],[],[],[],[]]
  let beforeLast : Fin 16 → List Bool := ![denominator,[],[],[],[],sign,numerator,[],[],[],[],[],[],[],[],[]]
  have first := move_executes 13 0 6 7 (by decide) (by decide) (by decide)
    (file numerator denominator [] [] [] sign) rfl
  change Executes (move 13 0 6 7) _ (6*numerator.length+4)
    (Function.update (Function.update (file numerator denominator [] [] [] sign) 6 (numerator++[])) 0 []) at first
  have firstStore : Function.update (Function.update (file numerator denominator [] [] [] sign) 6 (numerator++[])) 0 [] = middle := by
    funext r; fin_cases r <;> simp [middle,file]
  rw [firstStore] at first
  have second := move_executes 13 1 0 7 (by decide) (by decide) (by decide) middle rfl
  change Executes (move 13 1 0 7) middle (6*denominator.length+4)
    (Function.update (Function.update middle 0 (denominator++[])) 1 []) at second
  have secondStore : Function.update (Function.update middle 0 (denominator++[])) 1 [] = beforeLast := by
    funext r; fin_cases r <;> simp [middle,beforeLast]
  rw [secondStore] at second
  have third := move_executes 13 6 1 7 (by decide) (by decide) (by decide) beforeLast rfl
  change Executes (move 13 6 1 7) beforeLast (6*numerator.length+4)
    (Function.update (Function.update beforeLast 1 (numerator++[])) 6 []) at third
  have thirdStore : Function.update (Function.update beforeLast 1 (numerator++[])) 6 [] =
      file denominator numerator [] [] [] sign := by
    funext r; fin_cases r <;> simp [beforeLast,file]
  rw [thirdStore] at third
  convert first.sequence (second.sequence third) using 1
  omega

theorem inverse_raw_value (sign : Bool) (numerator denominator : Nat) :
    mkRat (Encoding.signedValue sign denominator) numerator =
      (mkRat (Encoding.signedValue sign numerator) denominator)⁻¹ := by
  cases sign <;> simp [Encoding.signedValue,Rat.mkRat_eq_div,inv_div,neg_div,inv_neg]

def inverseFunction (input : List Bool) : List Bool :=
  Encoding.rational.encode (mkRat
    (Encoding.signedValue (parsedSign input) (Encoding.value (parsed input).second))
    (Encoding.value (parsed input).first))

abbrev inverseRoutine : Routine 14 := sequence rationalParser
  (sequence swapOperands (sequence normalizationRoutine formatNormalized))

theorem inverse_computes : ComputesIn inverseRoutine.program inverseFunction
    (Complexity.polynomial 1500000 3) := by
  intro input
  obtain ⟨parseTime,parseBound,parsedRun⟩ := rationalParser_executes input
  let num := (parsed input).first
  let den := (parsed input).second
  let sign := parsedSign input
  let common := Nat.gcd (Encoding.value den) (Encoding.value num)
  let magnitude := reducedMagnitude (Encoding.value den) (Encoding.value num)
  let divisor := reducedDenominator (Encoding.value den) (Encoding.value num)
  have swapped := swapOperands_executes num den [sign]
  obtain ⟨normalizeTime,normalizeBound,normalized⟩ := normalization_executes den num [sign]
  obtain ⟨formatTime,formatBound,formatted⟩ := formatNormalized_executes den num common.bits magnitude divisor sign
  obtain ⟨finish,ran,halted,stored⟩ := parsedRun.sequence (swapped.sequence (normalized.sequence formatted))
  refine ⟨parseTime+1+(12*num.length+6*den.length+14+1+(normalizeTime+1+formatTime)),finish,?_,⟨?_,halted⟩,?_⟩
  · have lengths := parsed_lengths input
    change num.length+den.length ≤ input.length at lengths
    have numBits := EncodingPrograms.normalize_length_le num
    have denBits := EncodingPrograms.normalize_length_le den
    rw [Arithmetic.normalize_eq_bits,Encoding.bits_length] at numBits denBits
    have magnitudeSize := reducedMagnitude_size (Encoding.value den) (Encoding.value num)
    have divisorSize := reducedDenominator_size (Encoding.value den) (Encoding.value num)
    change magnitude.size ≤ (Encoding.value den).size at magnitudeSize
    change divisor.size ≤ (Encoding.value num).size+1 at divisorSize
    rw [Encoding.bits_length,Encoding.bits_length] at formatBound
    have normalizedBound := Nat.pow_le_pow_left
      (show den.length+num.length+1 ≤ input.length+1 by omega) 3
    have linear : input.length+1 ≤ (input.length+1)^3 := by
      have square := Nat.one_le_pow' 2 input.length
      have product := Nat.mul_le_mul_left (input.length+1) square
      nlinarith
    change _ ≤ 1500000*(input.length+1)^3
    omega
  · have start : initial inverseRoutine.program input = ⟨0,file input [] [] [] [] []⟩ := by
      apply congrArg (Config.mk _)
      funext r; fin_cases r <;> rfl
    rw [start]
    exact ran
  · rw [stored]
    exact (rational_encode_reduced sign (Encoding.value den) (Encoding.value num)).symm

theorem inverseFunction_raw (sign : Bool) (numerator denominator : Nat) (suffix : List Bool) :
    inverseFunction (sign::(Encoding.natural.encode numerator++Encoding.natural.encode denominator++suffix)) =
      Encoding.rational.encode ((mkRat (Encoding.signedValue sign numerator) denominator)⁻¹) := by
  simp only [inverseFunction,parsedSign,List.headD_cons,parsed,List.tail_cons,
    Encoding.natural,EncodingPrograms.parsePair_frames,Encoding.value_bits]
  exact congrArg Encoding.rational.encode (inverse_raw_value sign numerator denominator)

theorem inverseFunction_rational (value : Rat) :
    inverseFunction (Encoding.rational.encode value) = Encoding.rational.encode value⁻¹ := by
  rw [Encoding.rational_encode,Encoding.integer_encode,List.cons_append]
  have raw := inverseFunction_raw (Encoding.negative value.num) value.num.natAbs value.den []
  simp only [List.append_nil,Encoding.signedValue_negative_natAbs,Rat.mkRat_self] at raw
  exact raw

end Counting.StackMachine.RationalArithmetic
