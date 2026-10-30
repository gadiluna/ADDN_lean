import Counting.StackRationalPositiveIntegral
import Counting.StackCompilerComplete

namespace Counting.Machine
open StackMachine.RationalArithmetic.Predicates

def rationalPositiveIntegralProgram : Program := StackMachine.Compiler.compile positiveIntegralRoutine.program

theorem rationalPositiveIntegral_computesCleanIn : Complexity.ComputesCleanIn rationalPositiveIntegralProgram
    (fun input => Encoding.boolean.encode (positiveIntegralPredicate input)) (Complexity.polynomial (20*79^2) 2) := by
  have compiled := StackMachine.Compiler.computesCleanIn positiveIntegral_computes
  intro input
  obtain ⟨time,output,bounded,halted,tape⟩ := compiled input
  refine ⟨time,output,bounded.trans ?_,halted,tape⟩
  change 20*(input.length+14+60*(input.length+1)^1+4)^2 ≤ (20*79^2)*(input.length+1)^2
  simp only [pow_one]
  have base : input.length+14+60*(input.length+1)+4 ≤ 79*(input.length+1) := by omega
  calc
    _ ≤ 20*(79*(input.length+1))^2 := Nat.mul_le_mul_left 20 (Nat.pow_le_pow_left base 2)
    _ = _ := by ring

theorem rationalPositiveIntegral_rational_clean (value : Rat) :
    ∃ time output,
      time ≤ (20*79^2)*((Encoding.rational.encode value).length+1)^2 ∧
      HaltsAt rationalPositiveIntegralProgram (Encoding.rational.encode value) time output ∧
      output.tape.denotes = Turing.Tape.mk₁ ((Encoding.boolean.encode (decide (value.den=1 ∧ 0<value.num))).map bitSymbol) := by
  obtain ⟨time,output,bounded,halted,tape⟩ := rationalPositiveIntegral_computesCleanIn (Encoding.rational.encode value)
  refine ⟨time,output,bounded,halted,?_⟩
  dsimp only at tape
  rw [positiveIntegral_correct] at tape
  exact tape

end Counting.Machine
