import Counting.StackArithmeticTotal
import Counting.StackCompilerComplete

namespace Counting.Machine
open StackMachine.Arithmetic

def additionProgram : Program := StackMachine.Compiler.compile StackMachine.Arithmetic.additionProgram

/-- Binary addition is realized by a concrete finite-control Turing machine.
The bound includes frame parsing, stack representation, every tape shift,
normalization, output framing, bootstrap, and complete work-tape cleanup. -/
theorem addition_computesCleanIn :
    Complexity.ComputesCleanIn additionProgram additionFunction (Complexity.polynomial 8820 2) := by
  have compiled := StackMachine.Compiler.computesCleanIn addition_computes
  intro input
  obtain ⟨transitions, output, bounded, halted, tape⟩ := compiled input
  refine ⟨transitions, output, bounded.trans ?_, halted, tape⟩
  change 20*(input.length+5+(11*input.length+12)+4)^2 ≤ 8820*(input.length+1)^2
  have base : input.length+5+(11*input.length+12)+4 ≤ 21*(input.length+1) := by omega
  calc
    _ ≤ 20*(21*(input.length+1))^2 := Nat.mul_le_mul_left 20 (Nat.pow_le_pow_left base 2)
    _ = _ := by ring

theorem additionFunction_natural (first second : Nat) :
    additionFunction ((Encoding.product Encoding.natural Encoding.natural).encode (first,second)) =
      Encoding.natural.encode (first+second) := by
  simp only [Encoding.product, Encoding.natural, additionFunction, Encoding.unframe_frame, Encoding.value_bits]
  rw [show Encoding.unframe (Encoding.frame second.bits) = some (second.bits,[]) by
    simpa only [List.append_nil] using Encoding.unframe_frame second.bits []]
  simp only [Encoding.value_bits]

/-- The public arithmetic interface uses precisely the existing natural-pair
codec and returns the canonical natural codec on an entirely clean tape. -/
theorem addition_natural_clean (first second : Nat) :
    ∃ transitions output, transitions ≤ 8820*(2*first.size+2*second.size+3)^2 ∧
      HaltsAt additionProgram ((Encoding.product Encoding.natural Encoding.natural).encode (first,second)) transitions output ∧
      output.tape.denotes = Turing.Tape.mk₁ ((Encoding.natural.encode (first+second)).map bitSymbol) := by
  obtain ⟨transitions, output, bounded, halted, tape⟩ := addition_computesCleanIn
    ((Encoding.product Encoding.natural Encoding.natural).encode (first,second))
  refine ⟨transitions, output, ?_, halted, ?_⟩
  · simpa only [Complexity.polynomial, Encoding.product, List.length_append,
      Encoding.natural_length, show 2*first.size+1+(2*second.size+1)+1 =
        2*first.size+2*second.size+3 by omega] using bounded
  · rw [additionFunction_natural] at tape
    exact tape

end Counting.Machine
