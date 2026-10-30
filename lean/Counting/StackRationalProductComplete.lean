import Counting.StackRationalProductOutput
import Counting.StackRationalPairSpec

namespace Counting.StackMachine.RationalArithmetic.Product
open Routine

def parserRoles : Fin 9 ↪ Fin 20 := ⟨![0,1,2,3,4,5,6,7,8],by decide⟩
abbrev parser : Routine 18 := relocate Pair.parser parserRoles
abbrev completeProduct : Routine 18 := sequence parser (sequence productRoutine outputRoutine)
def productFunction (input : List Bool) : List Bool := Encoding.rational.encode (Pair.firstValue input*Pair.secondValue input)

theorem parser_executes (input : List Bool) :
    ∃ time ≤ 19*input.length+46,
      Executes parser (file input [] [] [] [] [] [] [] [] []) time
        (file (Pair.first input).first (Pair.first input).second (Pair.second input).first (Pair.second input).second
          [Pair.firstSign input] [Pair.secondSign input] [] [] [] []) := by
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

theorem product_computes : ComputesIn completeProduct.program productFunction (Complexity.polynomial 3000000 3) := by
  intro input
  let a := (Pair.first input).first
  let b := (Pair.first input).second
  let c := (Pair.second input).first
  let d := (Pair.second input).second
  let sa := Pair.firstSign input
  let sc := Pair.secondSign input
  let numerator := Encoding.value a*Encoding.value c
  let denominator := Encoding.value b*Encoding.value d
  let magnitude := reducedMagnitude numerator denominator
  let divisor := reducedDenominator numerator denominator
  obtain ⟨parseTime,parseBound,parsedRun⟩ := parser_executes input
  obtain ⟨coreTime,coreBound,coreRan⟩ := product_executes a b c d sa sc
  obtain ⟨outputTime,outputBound,outputRan⟩ := output_executes c d numerator.bits denominator.bits
    (Nat.gcd numerator denominator).bits magnitude divisor (xor sa sc)
  obtain ⟨finish,ran,halted,stored⟩ := parsedRun.sequence (coreRan.sequence outputRan)
  refine ⟨parseTime+1+(coreTime+1+outputTime),finish,?_,⟨?_,halted⟩,?_⟩
  · have lengths := Pair.parsed_lengths input
    change a.length+b.length+c.length+d.length+_ ≤ input.length at lengths
    have nbits := NaturalCall.product_bits_length a c
    have dbits := NaturalCall.product_bits_length b d
    change numerator.bits.length ≤ a.length+c.length at nbits
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
    change _ ≤ 3000000*(input.length+1)^3
    omega
  · have start : initial completeProduct.program input = ⟨0,file input [] [] [] [] [] [] [] [] []⟩ := by
      apply congrArg (Config.mk _)
      funext r; fin_cases r <;> simp [file]
    rw [start]
    exact ran
  · rw [stored]
    change Encoding.integer.encode (Encoding.signedValue (xor sa sc) magnitude)++Encoding.natural.encode divisor = _
    exact product_encoding sa sc (Encoding.value a) (Encoding.value b) (Encoding.value c) (Encoding.value d)

theorem productFunction_rationals (a b : Rat) :
    productFunction ((Encoding.product Encoding.rational Encoding.rational).encode (a,b)) = Encoding.rational.encode (a*b) := by
  simp only [productFunction,(Pair.values_rationals a b).1,(Pair.values_rationals a b).2]

end Counting.StackMachine.RationalArithmetic.Product
