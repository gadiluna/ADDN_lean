import Counting.ExternalCoefficientBounds

namespace Counting.External.CoefficientMachine
open StackMachine StackMachine.Routine MatchingMachine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

def computeCoefficients (word : List Bool) : List Bool :=
  match X3CEncoding.codec.decodeExact word with
  | none=>(Encoding.list Encoding.natural).encode []
  | some input=>(Encoding.list Encoding.natural).encode (inputCoefficients input)

theorem computeCoefficients_encoded (input : X3CEncoding.Input) :
    computeCoefficients (X3CEncoding.codec.encode input)=
      (Encoding.list Encoding.natural).encode (inputCoefficients input) := by
  have decoded := (X3CEncoding.codec.decodeExact_iff _ input).mpr rfl
  simp only [computeCoefficients,decoded]

def acceptedContinuation (extra : Nat) (w : Workspace extra) : Routine (extra+62) :=
  sequence (pushBit (w 1) true)
    (sequence (ofProgram (ListPrograms.copyProgram (extra+61) (w 51) (w 0) (w 63))) (coefficientGenerator extra w))
def rejectedContinuation (extra : Nat) (w : Workspace extra) : Routine (extra+62) :=
  prepend (w 1) ((Encoding.list Encoding.natural).encode [])
def typedGeneratorCost (input : X3CEncoding.Input) := generatorCost (X3CEncoding.codec.encode input).length
  input.1 input.2.1 ((Encoding.list Encoding.natural).encode (inputCoefficients input)).length

theorem acceptedContinuation_executes (extra : Nat) (w : Workspace extra)
    (store : Fin (extra+64) → List Bool) (input : X3CEncoding.Input)
    (backup : store (w 51)=X3CEncoding.codec.encode input) (source : store (w 0)=[])
    (status : store (w 1)=[]) (population : store (w 17)=List.replicate (3*input.1) true)
    (count : store (w 25)=List.replicate input.2.1 true)
    (empty : ∀ i∈MatchingMachine.generatorScratch,store (w i)=[]) :
    ∃ time ≤ typedGeneratorCost input+5*(X3CEncoding.codec.encode input).length+5,
      ∃ result,Executes (acceptedContinuation extra w) store time result ∧
        result (w 1)=(Encoding.list Encoding.natural).encode (inputCoefficients input) := by
  have pushing:=pushBit_executes (w 1) true store
  rw [status] at pushing
  let flagged:=Function.update store (w 1) [true]
  have copying:=copy_executes (extra+61) (w 51) (w 0) (w 63)
    (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) flagged
    (by simp [flagged,w.injective.eq_iff,empty 63 (by simp [MatchingMachine.generatorScratch])])
  have b : flagged (w 51)=X3CEncoding.codec.encode input := by simp [flagged,w.injective.eq_iff,backup]
  have s : flagged (w 0)=[] := by simp [flagged,w.injective.eq_iff,source]
  rw [b,s,List.append_nil] at copying
  let restored:=Function.update flagged (w 0) (X3CEncoding.codec.encode input)
  have preparedEmpty (i : Fin 64) (member : i∈MatchingMachine.generatorScratch) : restored (w i)=[] := by
    have a : i≠0 := by intro equal;subst i;simp [MatchingMachine.generatorScratch] at member
    have b : i≠1 := by intro equal;subst i;simp [MatchingMachine.generatorScratch] at member
    simp [restored,flagged,w.injective.eq_iff,a,b,empty i member]
  obtain ⟨time,bound,result,running,output⟩:=coefficientGenerator_executes extra w restored input
    (by simp [restored]) (by simp [restored,flagged,w.injective.eq_iff])
    (by simp [restored,flagged,w.injective.eq_iff,population])
    (by simp [restored,flagged,w.injective.eq_iff,count]) preparedEmpty
  have typedBound : time ≤ typedGeneratorCost input := by
    simpa [restored,typedGeneratorCost] using bound
  exact ⟨1+1+(5*(X3CEncoding.codec.encode input).length+2+1+time),by omega,result,
    pushing.sequence (copying.sequence running),output⟩

end Counting.External.CoefficientMachine
