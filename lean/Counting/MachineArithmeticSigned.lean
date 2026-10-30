import Counting.StackSignedComplete
import Counting.StackCompilerComplete

namespace Counting.Machine
open StackMachine.Signed

def signedAdditionProgram : Program := StackMachine.Compiler.compile signedAdditionRoutine.program

/-- The finite Turing program includes sign parsing, magnitude comparison,
addition/subtraction, canonical zero, every tape shift, and final cleanup. -/
theorem signedAddition_computesCleanIn :
    Complexity.ComputesCleanIn signedAdditionProgram signedAdditionFunction (Complexity.polynomial 300000 2) := by
  have compiled := StackMachine.Compiler.computesCleanIn signedAddition_computes
  intro input
  obtain ⟨time,output,bounded,halted,tape⟩ := compiled input
  refine ⟨time,output,bounded.trans ?_,halted,tape⟩
  change 20*(input.length+10+100*(input.length+1)^1+4)^2 ≤ 300000*(input.length+1)^2
  rw [pow_one]
  have base : input.length+10+100*(input.length+1)+4 ≤ 115*(input.length+1) := by omega
  calc
    _ ≤ 20*(115*(input.length+1))^2 := Nat.mul_le_mul_left 20 (Nat.pow_le_pow_left base 2)
    _ = 264500*(input.length+1)^2 := by ring
    _ ≤ _ := Nat.mul_le_mul_right _ (by decide)

theorem signedAddition_integer_clean (first second : Int) :
    ∃ time output, time ≤ 300000*(2*first.natAbs.size+2*second.natAbs.size+5)^2 ∧
      HaltsAt signedAdditionProgram ((Encoding.product Encoding.integer Encoding.integer).encode (first,second)) time output ∧
      output.tape.denotes = Turing.Tape.mk₁ ((Encoding.integer.encode (first+second)).map bitSymbol) := by
  obtain ⟨time,output,bounded,halted,tape⟩ := signedAddition_computesCleanIn
    ((Encoding.product Encoding.integer Encoding.integer).encode (first,second))
  refine ⟨time,output,?_,halted,?_⟩
  · simpa only [Complexity.polynomial,Encoding.product,List.length_append,Encoding.integer_length,
      show 2*first.natAbs.size+2+(2*second.natAbs.size+2)+1 =
        2*first.natAbs.size+2*second.natAbs.size+5 by omega] using bounded
  · rw [signedAdditionFunction_integer] at tape
    exact tape

end Counting.Machine
