import Counting.StackRationalBasic
import Counting.StackCompilerComplete

namespace Counting.Machine
open StackMachine

def rationalCastStack : StackMachine.Program := (RationalArithmetic.castNatural 0 0 1 2).program

theorem rationalCast_stack_computes : StackMachine.ComputesIn rationalCastStack
    (fun input => Encoding.rational.encode (Encoding.value input:Rat)) (fun length => 5*length+13) := by
  intro input
  let store : Fin 3 → List Bool := fun r => if r=0 then input else []
  obtain ⟨finish,ran,halted,stored⟩ := RationalArithmetic.castNatural_executes 0 0 1 2
    (by decide) (by decide) (by decide) store rfl
  refine ⟨Normalize.formatCost input+9,finish,RationalArithmetic.castNatural_cost input,⟨ran,halted⟩,?_⟩
  rw [stored]
  exact List.append_nil _

def rationalCastProgram : Program := Compiler.compile rationalCastStack

/-- Input is the raw little-endian payload used by arithmetic register
interfaces, and output is the full canonical rational codec. -/
theorem rationalCast_computesCleanIn : Complexity.ComputesCleanIn rationalCastProgram
    (fun input => Encoding.rational.encode (Encoding.value input:Rat)) (Complexity.polynomial 6480 2) := by
  have compiled := Compiler.computesCleanIn rationalCast_stack_computes
  intro input
  obtain ⟨time,output,bounded,halted,tape⟩ := compiled input
  refine ⟨time,output,bounded.trans ?_,halted,tape⟩
  change 20*(input.length+1+(5*input.length+13)+4)^2 ≤ 6480*(input.length+1)^2
  have base : input.length+1+(5*input.length+13)+4 ≤ 18*(input.length+1) := by omega
  calc
    _ ≤ 20*(18*(input.length+1))^2 := Nat.mul_le_mul_left 20 (Nat.pow_le_pow_left base 2)
    _ = _ := by ring

theorem rationalCast_natural_clean (value : Nat) :
    ∃ time output, time ≤ 6480*(value.size+1)^2 ∧
      HaltsAt rationalCastProgram value.bits time output ∧
      output.tape.denotes = Turing.Tape.mk₁ ((Encoding.rational.encode (value:Rat)).map bitSymbol) := by
  obtain ⟨time,output,bounded,halted,tape⟩ := rationalCast_computesCleanIn value.bits
  refine ⟨time,output,?_,halted,?_⟩
  · simpa only [Complexity.polynomial,Encoding.bits_length] using bounded
  · simpa only [Encoding.value_bits] using tape

end Counting.Machine
