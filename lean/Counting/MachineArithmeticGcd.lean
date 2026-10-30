import Counting.StackBinaryGcdOutput
import Counting.StackCompilerComplete

namespace Counting.Machine
open StackMachine.Binary.Gcd

def gcdProgram : Program := StackMachine.Compiler.compile gcdRoutine.program

/-- A concrete finite-control Turing machine for binary gcd. Unary control
counts input bits only; Euclidean arithmetic uses verified binary long
division. The bound includes parsing, counters, every tape shift and cleanup. -/
theorem gcd_computesCleanIn :
    Complexity.ComputesCleanIn gcdProgram gcdFunction (Complexity.polynomial 20808000 6) := by
  have compiled := StackMachine.Compiler.computesCleanIn gcd_computes
  intro input
  obtain ⟨transitions,output,bounded,halted,tape⟩ := compiled input
  refine ⟨transitions,output,bounded.trans ?_,halted,tape⟩
  change 20*(input.length+8+1000*(input.length+1)^3+4)^2 ≤ 20808000*(input.length+1)^6
  have positive := Nat.one_le_pow' 3 input.length
  have linear : input.length+1 ≤ (input.length+1)^3 := by
    have square := Nat.one_le_pow' 2 input.length
    have product := Nat.mul_le_mul_left (input.length+1) square
    nlinarith
  have base : input.length+8+1000*(input.length+1)^3+4 ≤ 1020*(input.length+1)^3 := by omega
  calc
    _ ≤ 20*(1020*(input.length+1)^3)^2 := Nat.mul_le_mul_left 20 (Nat.pow_le_pow_left base 2)
    _ = _ := by ring

/-- Canonical gcd on a completely clean tape, for the actual pair codec,
including both zero operands. -/
theorem gcd_natural_clean (first second : Nat) :
    ∃ transitions output, transitions ≤ 20808000*(2*first.size+2*second.size+3)^6 ∧
      HaltsAt gcdProgram ((Encoding.product Encoding.natural Encoding.natural).encode (first,second)) transitions output ∧
      output.tape.denotes = Turing.Tape.mk₁ ((Encoding.natural.encode (Nat.gcd first second)).map bitSymbol) := by
  obtain ⟨transitions,output,bounded,halted,tape⟩ := gcd_computesCleanIn
    ((Encoding.product Encoding.natural Encoding.natural).encode (first,second))
  refine ⟨transitions,output,?_,halted,?_⟩
  · simpa only [Complexity.polynomial,Encoding.product,List.length_append,
      Encoding.natural_length,show 2*first.size+1+(2*second.size+1)+1 =
        2*first.size+2*second.size+3 by omega] using bounded
  · rw [gcdFunction_natural] at tape
    exact tape

end Counting.Machine
