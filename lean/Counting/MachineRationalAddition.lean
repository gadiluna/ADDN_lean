import Counting.StackRationalAddComplete
import Counting.StackCompilerComplete

namespace Counting.Machine
open StackMachine.RationalArithmetic.Addition

def rationalAdditionProgram : Program := StackMachine.Compiler.compile completeAddition.program

theorem rationalAddition_computesCleanIn : Complexity.ComputesCleanIn rationalAdditionProgram
    additionFunction (Complexity.polynomial (20*(14000000+20+5)^2) 6) := by
  have compiled := StackMachine.Compiler.computesCleanIn addition_computes
  intro input
  obtain ⟨time,output,bounded,halted,tape⟩ := compiled input
  refine ⟨time,output,bounded.trans ?_,halted,tape⟩
  change 20*(input.length+20+14000000*(input.length+1)^3+4)^2 ≤
    (20*(14000000+20+5)^2)*(input.length+1)^6
  have linear : input.length+1 ≤ (input.length+1)^3 := by
    have square := Nat.one_le_pow' 2 input.length
    have product := Nat.mul_le_mul_left (input.length+1) square
    nlinarith
  have positive := Nat.one_le_pow' 3 input.length
  have base : input.length+20+14000000*(input.length+1)^3+4 ≤
      (14000000+20+5)*(input.length+1)^3 := by omega
  calc
    _ ≤ 20*((14000000+20+5)*(input.length+1)^3)^2 :=
      Nat.mul_le_mul_left 20 (Nat.pow_le_pow_left base 2)
    _ = _ := by ring

theorem rationalAddition_rationals_clean (a b : Rat) :
    ∃ time output,
      time ≤ (20*(14000000+20+5)^2)*(((Encoding.product Encoding.rational Encoding.rational).encode (a,b)).length+1)^6 ∧
      HaltsAt rationalAdditionProgram ((Encoding.product Encoding.rational Encoding.rational).encode (a,b)) time output ∧
      output.tape.denotes = Turing.Tape.mk₁ ((Encoding.rational.encode (a+b)).map bitSymbol) := by
  obtain ⟨time,output,bounded,halted,tape⟩ := rationalAddition_computesCleanIn
    ((Encoding.product Encoding.rational Encoding.rational).encode (a,b))
  refine ⟨time,output,bounded,halted,?_⟩
  rw [additionFunction_rationals] at tape
  exact tape

end Counting.Machine
