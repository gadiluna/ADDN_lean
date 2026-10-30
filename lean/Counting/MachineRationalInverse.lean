import Counting.StackRationalInverse

namespace Counting.Machine
open StackMachine.RationalArithmetic

def rationalInverseProgram : Program := StackMachine.Compiler.compile inverseRoutine.program

theorem rationalInverse_computesCleanIn : Complexity.ComputesCleanIn rationalInverseProgram
    inverseFunction (Complexity.polynomial (20*(1500000+14+5)^2) 6) := by
  have compiled := StackMachine.Compiler.computesCleanIn inverse_computes
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

theorem rationalInverse_rational_clean (value : Rat) :
    ∃ time output,
      time ≤ (20*(1500000+14+5)^2)*(2*(value.num.natAbs.size+value.den.size)+4)^6 ∧
      HaltsAt rationalInverseProgram (Encoding.rational.encode value) time output ∧
      output.tape.denotes = Turing.Tape.mk₁ ((Encoding.rational.encode value⁻¹).map bitSymbol) := by
  obtain ⟨time,output,bounded,halted,tape⟩ := rationalInverse_computesCleanIn (Encoding.rational.encode value)
  refine ⟨time,output,?_,halted,?_⟩
  · simpa only [Complexity.polynomial,Encoding.rational_length,Nat.add_assoc] using bounded
  · rw [inverseFunction_rational] at tape
    exact tape

theorem rationalInverse_raw_clean (sign : Bool) (numerator denominator : Nat) (suffix : List Bool) :
    ∃ time output,
      time ≤ (20*(1500000+14+5)^2)*(2*numerator.size+2*denominator.size+suffix.length+4)^6 ∧
      HaltsAt rationalInverseProgram
        (sign::(Encoding.natural.encode numerator++Encoding.natural.encode denominator++suffix)) time output ∧
      output.tape.denotes = Turing.Tape.mk₁
        ((Encoding.rational.encode ((mkRat (Encoding.signedValue sign numerator) denominator)⁻¹)).map bitSymbol) := by
  obtain ⟨time,output,bounded,halted,tape⟩ := rationalInverse_computesCleanIn
    (sign::(Encoding.natural.encode numerator++Encoding.natural.encode denominator++suffix))
  refine ⟨time,output,?_,halted,?_⟩
  · simpa only [Complexity.polynomial,List.length_cons,List.length_append,Encoding.natural_length,
      show 2*numerator.size+1+(2*denominator.size+1)+suffix.length+1+1 =
        2*numerator.size+2*denominator.size+suffix.length+4 by omega] using bounded
  · rw [inverseFunction_raw] at tape
    exact tape

end Counting.Machine
