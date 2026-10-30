import Counting.StackEncodingListExact

namespace Counting.StackMachine.EncodingPrograms

/-- Input register zero, Boolean output register one, and fifteen restored
workspace registers. The reusable prefix routine also exposes parsed fields. -/
def listRecognitionProgram : Program :=
  (listExactRoutine 0 (Function.Embedding.refl (Fin 17))).program

theorem list_computes : ComputesIn listRecognitionProgram
    (fun input => [((Encoding.list Encoding.natural).decodeExact input).isSome])
    (Complexity.polynomial 1920 3) := by
  intro input
  let store : Fin 17 → List Bool := fun r => if r=0 then input else []
  have empty (i : Fin 17) (h0 : i≠0) (_h1 : i≠1) : store i=[] := by simp [store,h0]
  obtain ⟨time,bounded,finish,ran,halted,output⟩:=listExact_executes 0 (Function.Embedding.refl (Fin 17)) store empty
  refine ⟨time,finish,bounded,⟨ran,halted⟩,?_⟩
  rw [output]
  change [listCheck input]=_
  rw [listCheck_decodeExact]

/-- This bound counts transitions of the compiled finite Turing machine and
requires the entire output tape to be clean, including on invalid inputs. -/
theorem list_computesCleanIn : Complexity.ComputesCleanIn (Compiler.compile listRecognitionProgram)
    (fun input => [((Encoding.list Encoding.natural).decodeExact input).isSome])
    (Complexity.polynomial 75272000 8) := by
  exact Compiler.computesCleanIn_polynomial 1920 3 list_computes

end Counting.StackMachine.EncodingPrograms
