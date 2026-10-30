import Counting.StackBinaryMultiplyOutput
import Counting.StackCompilerComplete

namespace Counting.Machine
open StackMachine.Binary

def multiplicationProgram : Program := StackMachine.Compiler.compile multiplicationRoutine.program

/-- A concrete single-tape finite-control machine computes binary products.
The polynomial includes both frame parsers, shift-add, normalization, every
physical stack simulation, bootstrap, and complete work-tape cleanup. -/
theorem multiplication_computesCleanIn :
    Complexity.ComputesCleanIn multiplicationProgram productFunction (Complexity.polynomial 242000 6) := by
  have compiled := StackMachine.Compiler.computesCleanIn multiplication_computes
  intro input
  obtain ⟨transitions,output,bounded,halted,tape⟩ := compiled input
  refine ⟨transitions,output,bounded.trans ?_,halted,tape⟩
  change 20*(input.length+5+100*(input.length+1)^3+4)^2 ≤ 242000*(input.length+1)^6
  have positive := Nat.one_le_pow' 3 input.length
  have linear := cubic_dominates_linear input.length
  have base : input.length+5+100*(input.length+1)^3+4 ≤ 110*(input.length+1)^3 := by omega
  calc
    _ ≤ 20*(110*(input.length+1)^3)^2 := Nat.mul_le_mul_left 20 (Nat.pow_le_pow_left base 2)
    _ = _ := by ring

/-- Public multiplication uses the existing pair-of-naturals codec and
returns its canonical product on a completely clean tape. -/
theorem multiplication_natural_clean (first second : Nat) :
    ∃ transitions output, transitions ≤ 242000*(2*first.size+2*second.size+3)^6 ∧
      HaltsAt multiplicationProgram ((Encoding.product Encoding.natural Encoding.natural).encode (first,second)) transitions output ∧
      output.tape.denotes = Turing.Tape.mk₁ ((Encoding.natural.encode (first*second)).map bitSymbol) := by
  obtain ⟨transitions,output,bounded,halted,tape⟩ := multiplication_computesCleanIn
    ((Encoding.product Encoding.natural Encoding.natural).encode (first,second))
  refine ⟨transitions,output,?_,halted,?_⟩
  · simpa only [Complexity.polynomial,Encoding.product,List.length_append,
      Encoding.natural_length,show 2*first.size+1+(2*second.size+1)+1 =
        2*first.size+2*second.size+3 by omega] using bounded
  · rw [productFunction_natural] at tape
    exact tape

end Counting.Machine
