import Counting.StackBinaryDivisionOutput
import Counting.StackCompilerComplete

namespace Counting.Machine
open StackMachine.Binary.Division

def divisionProgram : Program := StackMachine.Compiler.compile divisionRoutine.program

/-- Concrete single-tape binary long division, with total parsing and a
zero-divisor branch. All tape operations and cleanup are included. -/
theorem division_computesCleanIn :
    Complexity.ComputesCleanIn divisionProgram quotientFunction (Complexity.polynomial 800000 4) := by
  have compiled := StackMachine.Compiler.computesCleanIn division_computes
  intro input
  obtain ⟨transitions,output,bounded,halted,tape⟩ := compiled input
  refine ⟨transitions,output,bounded.trans ?_,halted,tape⟩
  change 20*(input.length+8+180*(input.length+1)^2+4)^2 ≤ 800000*(input.length+1)^4
  have base : input.length+8+180*(input.length+1)^2+4 ≤ 200*(input.length+1)^2 := by nlinarith
  calc
    _ ≤ 20*(200*(input.length+1)^2)^2 := Nat.mul_le_mul_left 20 (Nat.pow_le_pow_left base 2)
    _ = _ := by ring

/-- Canonical quotient, including the natural convention a/0=0, on a
completely clean tape and using the exact existing pair codec. -/
theorem division_natural_clean (first second : Nat) :
    ∃ transitions output, transitions ≤ 800000*(2*first.size+2*second.size+3)^4 ∧
      HaltsAt divisionProgram ((Encoding.product Encoding.natural Encoding.natural).encode (first,second)) transitions output ∧
      output.tape.denotes = Turing.Tape.mk₁ ((Encoding.natural.encode (first/second)).map bitSymbol) := by
  obtain ⟨transitions,output,bounded,halted,tape⟩ := division_computesCleanIn
    ((Encoding.product Encoding.natural Encoding.natural).encode (first,second))
  refine ⟨transitions,output,?_,halted,?_⟩
  · simpa only [Complexity.polynomial,Encoding.product,List.length_append,
      Encoding.natural_length,show 2*first.size+1+(2*second.size+1)+1 =
        2*first.size+2*second.size+3 by omega] using bounded
  · rw [quotientFunction_natural] at tape
    exact tape

end Counting.Machine
