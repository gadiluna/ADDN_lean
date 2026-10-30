import Counting.StackSignedMultiplyComplete
import Counting.StackCompilerComplete

namespace Counting.Machine
open StackMachine.Signed.Multiply

def signedProductProgram : Program := StackMachine.Compiler.compile productRoutine.program

theorem signedProduct_computesCleanIn :
    Complexity.ComputesCleanIn signedProductProgram signedProductFunction (Complexity.polynomial 300000 6) := by
  have compiled := StackMachine.Compiler.computesCleanIn signedProduct_computes
  intro input
  obtain ⟨time,output,bounded,halted,tape⟩ := compiled input
  refine ⟨time,output,bounded.trans ?_,halted,tape⟩
  change 20*(input.length+10+100*(input.length+1)^3+4)^2 ≤ 300000*(input.length+1)^6
  have linear : input.length+1 ≤ (input.length+1)^3 := by
    have square := Nat.one_le_pow' 2 input.length
    have product := Nat.mul_le_mul_left (input.length+1) square
    nlinarith
  have positive := Nat.one_le_pow' 3 input.length
  have base : input.length+10+100*(input.length+1)^3+4 ≤ 115*(input.length+1)^3 := by omega
  calc
    _ ≤ 20*(115*(input.length+1)^3)^2 := Nat.mul_le_mul_left 20 (Nat.pow_le_pow_left base 2)
    _ = 264500*(input.length+1)^6 := by ring
    _ ≤ _ := Nat.mul_le_mul_right _ (by decide)

theorem signedProduct_integer_clean (first second : Int) :
    ∃ time output, time ≤ 300000*(2*first.natAbs.size+2*second.natAbs.size+5)^6 ∧
      HaltsAt signedProductProgram ((Encoding.product Encoding.integer Encoding.integer).encode (first,second)) time output ∧
      output.tape.denotes = Turing.Tape.mk₁ ((Encoding.integer.encode (first*second)).map bitSymbol) := by
  obtain ⟨time,output,bounded,halted,tape⟩ := signedProduct_computesCleanIn
    ((Encoding.product Encoding.integer Encoding.integer).encode (first,second))
  refine ⟨time,output,?_,halted,?_⟩
  · simpa only [Complexity.polynomial,Encoding.product,List.length_append,Encoding.integer_length,
      show 2*first.natAbs.size+2+(2*second.natAbs.size+2)+1 =
        2*first.natAbs.size+2*second.natAbs.size+5 by omega] using bounded
  · rw [signedProductFunction_integer] at tape
    exact tape

end Counting.Machine
