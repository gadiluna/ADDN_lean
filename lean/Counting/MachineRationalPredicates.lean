import Counting.StackRationalPredicateSpec
import Counting.StackCompilerComplete

namespace Counting.Machine
open StackMachine.RationalArithmetic.Predicates

def rationalPredicateProgram (kind : Kind) : Program := StackMachine.Compiler.compile (routine kind).program

theorem rationalPredicate_computesCleanIn (kind : Kind) : Complexity.ComputesCleanIn (rationalPredicateProgram kind)
    (fun input => Encoding.boolean.encode (predicate kind input)) (Complexity.polynomial (20*69^2) 2) := by
  have compiled := StackMachine.Compiler.computesCleanIn (predicate_computes kind)
  intro input
  obtain ⟨time,output,bounded,halted,tape⟩ := compiled input
  refine ⟨time,output,bounded.trans ?_,halted,tape⟩
  change 20*(input.length+14+50*(input.length+1)^1+4)^2 ≤ (20*69^2)*(input.length+1)^2
  simp only [pow_one]
  have base : input.length+14+50*(input.length+1)+4 ≤ 69*(input.length+1) := by omega
  calc
    _ ≤ 20*(69*(input.length+1))^2 := Nat.mul_le_mul_left 20 (Nat.pow_le_pow_left base 2)
    _ = _ := by ring

def rationalPredicateSpec : Kind → Rat → Bool
  | .zero, value => decide (value=0)
  | .negative, value => decide (value<0)
  | .positive, value => decide (0<value)
  | .integral, value => decide (value.den=1)

theorem rationalPredicate_rational_clean (kind : Kind) (value : Rat) :
    ∃ time output,
      time ≤ (20*69^2)*((Encoding.rational.encode value).length+1)^2 ∧
      HaltsAt (rationalPredicateProgram kind) (Encoding.rational.encode value) time output ∧
      output.tape.denotes = Turing.Tape.mk₁
        ((Encoding.boolean.encode (rationalPredicateSpec kind value)).map bitSymbol) := by
  obtain ⟨time,output,bounded,halted,tape⟩ := rationalPredicate_computesCleanIn kind (Encoding.rational.encode value)
  refine ⟨time,output,bounded,halted,?_⟩
  have result : predicate kind (Encoding.rational.encode value) = rationalPredicateSpec kind value := by
    cases kind
    · exact zero_correct value
    · exact negative_correct value
    · exact positive_correct value
    · exact integral_correct value
  dsimp only at tape
  rw [result] at tape
  exact tape

end Counting.Machine
