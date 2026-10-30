import Counting.StackEncodingPairSemantics

namespace Counting.StackMachine.EncodingPrograms

/-- Register one is the Boolean output of the standalone recognition machine;
the generic routine still exposes both payload registers and the suffix. -/
def pairRecognitionRegisters : Fin 5 → Fin 5 := ![0,2,3,4,1]

theorem pairRecognitionRegisters_injective : Function.Injective pairRecognitionRegisters := by decide

def pairRecognitionProgram : Program := (pairRoutine 0 pairRecognitionRegisters).program

theorem parsePair_accepted (input : List Bool) :
    (parsePair input).accepted = ((Encoding.product frameCodec frameCodec).decode input).isSome := by
  rw [parsePair_codec]
  cases result : (parsePair input).accepted <;> rfl

theorem pair_computes : ComputesIn pairRecognitionProgram
    (fun input => [((Encoding.product frameCodec frameCodec).decode input).isSome])
    (fun length => 6*length+13) := by
  intro input
  let store : Fin 5 → List Bool := fun r => if r=0 then input else []
  have empty : store (pairRecognitionRegisters 3)=[] := rfl
  obtain ⟨time,bounded,finish,executed,halted,output⟩ := pair_executes_spec 0 pairRecognitionRegisters
    pairRecognitionRegisters_injective store empty
  refine ⟨time,finish,bounded,⟨executed,halted⟩,?_⟩
  rw [output]
  change [((parsePair input).accepted)] = _
  rw [parsePair_accepted]

theorem pair_computesCleanIn : Complexity.ComputesCleanIn (Compiler.compile pairRecognitionProgram)
    (fun input => [((Encoding.product frameCodec frameCodec).decode input).isSome])
    (Complexity.polynomial (20*(13+3+5)^2) 4) := by
  apply Compiler.computesCleanIn_polynomial 13 1
  intro input
  obtain ⟨time,output,bound,halted,value⟩ := pair_computes input
  refine ⟨time,output,?_,halted,value⟩
  simp only [Complexity.polynomial,pow_one]
  dsimp only at bound
  omega

end Counting.StackMachine.EncodingPrograms
