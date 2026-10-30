import Counting.StackUnaryBinary
import Counting.StackCompilerComplete

namespace Counting.Machine
open StackMachine

def unaryLengthProgram : Program := Compiler.compile (Unary.lengthProgram 0 0 1 2)
def unaryToBinaryProgram : Program := Compiler.compile (Unary.toBinaryProgram 0 0 1 2)

/-- Compute an explicit unary length counter with a genuine tape-step bound. -/
theorem unaryLength_computesCleanIn : Complexity.ComputesCleanIn unaryLengthProgram
    (fun input => List.replicate input.length true) (Complexity.polynomial 980 2) := by
  have compiled := Compiler.computesCleanIn Unary.length_computes
  intro input
  obtain ⟨transitions, output, bounded, halted, tape⟩ := compiled input
  refine ⟨transitions, output, bounded.trans ?_, halted, tape⟩
  change 20*(input.length+1+(5*input.length+2)+4)^2 ≤ 980*(input.length+1)^2
  have base : input.length+1+(5*input.length+2)+4 ≤ 7*(input.length+1) := by omega
  calc
    _ ≤ 20*(7*(input.length+1))^2 := Nat.mul_le_mul_left 20 (Nat.pow_le_pow_left base 2)
    _ = _ := by ring

/-- Convert a unary counter to its canonical binary payload, including all
stack simulation and cleanup costs on the concrete Turing machine. -/
theorem unaryToBinary_computesCleanIn : Complexity.ComputesCleanIn unaryToBinaryProgram
    (fun input => input.length.bits) (Complexity.polynomial 720 4) := by
  have compiled := Compiler.computesCleanIn Unary.toBinary_computes
  intro input
  obtain ⟨transitions, output, bounded, halted, tape⟩ := compiled input
  refine ⟨transitions, output, bounded.trans ?_, halted, tape⟩
  change 20*(input.length+1+(4*input.length*(input.length+1)+1)+4)^2 ≤ 720*(input.length+1)^4
  have base : input.length+1+(4*input.length*(input.length+1)+1)+4 ≤ 6*(input.length+1)^2 := by nlinarith
  calc
    _ ≤ 20*(6*(input.length+1)^2)^2 := Nat.mul_le_mul_left 20 (Nat.pow_le_pow_left base 2)
    _ = _ := by ring

theorem unaryToBinary_natural (count : Nat) :
    ∃ transitions output, transitions ≤ 720*(count+1)^4 ∧
      HaltsAt unaryToBinaryProgram (List.replicate count true) transitions output ∧
      output.tape.denotes = Turing.Tape.mk₁ (count.bits.map bitSymbol) := by
  simpa only [List.length_replicate, Complexity.polynomial] using
    unaryToBinary_computesCleanIn (List.replicate count true)

end Counting.Machine
