import Counting.StackNormalize
import Counting.StackCompilerComplete

namespace Counting.Machine
open StackMachine

def normalizationStack : StackMachine.Program := (Normalize.formatRoutine 0 0 1 2).program

theorem normalization_stack_computes : StackMachine.ComputesIn normalizationStack
    (fun input => Encoding.natural.encode (Encoding.value input)) (fun length => 5*length+4) := by
  intro input
  let initialStore : Fin 3 → List Bool := fun r => if r=0 then input else []
  have executed := Normalize.format_executes 0 0 1 2 (by decide) (by decide) (by decide)
    initialStore (by rfl)
  obtain ⟨finish,ran,halted,store⟩ := executed
  refine ⟨Normalize.formatCost input,finish,Normalize.formatCost_le input,⟨ran,halted⟩,?_⟩
  rw [store]
  change Encoding.natural.encode (Encoding.value input)++[]=Encoding.natural.encode (Encoding.value input)
  exact List.append_nil _

def normalizationProgram : Program := Compiler.compile normalizationStack

/-- Total normalization includes arbitrarily many redundant high zeroes,
framing, and cleanup of the entire tape in the actual machine model. -/
theorem normalization_computesCleanIn : Complexity.ComputesCleanIn normalizationProgram
    (fun input => Encoding.natural.encode (Encoding.value input)) (Complexity.polynomial 1620 2) := by
  have compiled := Compiler.computesCleanIn normalization_stack_computes
  intro input
  obtain ⟨steps,finish,bounded,halted,tape⟩ := compiled input
  refine ⟨steps,finish,bounded.trans ?_,halted,tape⟩
  change 20*(input.length+1+(5*input.length+4)+4)^2 ≤ 1620*(input.length+1)^2
  have base : input.length+1+(5*input.length+4)+4 ≤ 9*(input.length+1) := by omega
  calc
    _ ≤ 20*(9*(input.length+1))^2 := Nat.mul_le_mul_left 20 (Nat.pow_le_pow_left base 2)
    _ = _ := by ring

end Counting.Machine
