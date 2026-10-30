import Counting.ExternalCoverNormalizePolynomial
import Counting.ExternalCoverReduction
import Counting.ExternalCoverInputValidation

namespace Counting.External.CoverNormalization
open StackMachine StackMachine.Routine MatchingMachine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

def rejectedOutput : List Bool := X3CEncoding.codec.encode (X3CEncoding.normalizedInput CoverMachine.rejectCover)

def normalizeWord (word : List Bool) : List Bool :=
  match X3CEncoding.codec.decodeExact word with
  | none=>rejectedOutput
  | some input=>X3CEncoding.codec.encode (X3CEncoding.normalizedInput input)

theorem normalizeWord_encoded (input : X3CEncoding.Input) :
    normalizeWord (X3CEncoding.codec.encode input)=X3CEncoding.codec.encode (X3CEncoding.normalizedInput input) := by
  have decoded := (X3CEncoding.codec.decodeExact_iff _ input).mpr rfl
  simp only [normalizeWord,decoded]

theorem normalizeWord_yes_iff (word : List Bool) :
    X3CEncoding.BinaryX3C (normalizeWord word) ↔ X3CEncoding.BinaryX3C word := by
  have rejected : ¬X3CEncoding.BinaryX3C rejectedOutput := by
    rw [rejectedOutput,X3CEncoding.encoded_yes_iff,X3CEncoding.normalizedInput_exactCover]
    exact CoverMachine.rejectCover_no
  cases decoded : X3CEncoding.codec.decodeExact word with
  | none=>
    have absent : ¬X3CEncoding.BinaryX3C word := by
      rintro ⟨input,encoded,_⟩
      rw [decoded] at encoded
      cases encoded
    simp [normalizeWord,decoded,absent,rejected]
  | some input=>
    have encoded := (X3CEncoding.codec.decodeExact_iff word input).mp decoded
    rw [←encoded,normalizeWord_encoded,X3CEncoding.encoded_yes_iff,
      X3CEncoding.normalizedInput_exactCover,X3CEncoding.encoded_yes_iff]

def acceptedContinuation (extra : Nat) (w : GeneratorWorkspace extra) : Routine (extra+62) :=
  sequence (pushBit (w 1) true)
    (sequence (ofProgram (ListPrograms.copyProgram (extra+61) (w 51) (w 0) (w 63))) (generator extra w))

def rejectedContinuation (extra : Nat) (w : GeneratorWorkspace extra) : Routine (extra+62) :=
  prepend (w 1) rejectedOutput

def typedGeneratorCost (input : X3CEncoding.Input) :=
  generatorCost (X3CEncoding.codec.encode input).length (CoverInputValidation.inputRaw input)

theorem acceptedContinuation_executes (extra : Nat) (w : GeneratorWorkspace extra)
    (store : Fin (extra+64)→List Bool) (input : X3CEncoding.Input)
    (backup : store (w 51)=X3CEncoding.codec.encode input) (source : store (w 0)=[])
    (status : store (w 1)=[]) (population : store (w 17)=List.replicate (3*input.1) true)
    (empty : ∀ i∈MatchingMachine.generatorScratch,store (w i)=[]) :
    ∃ time ≤ typedGeneratorCost input+5*(X3CEncoding.codec.encode input).length+5,
      ∃ result,Executes (acceptedContinuation extra w) store time result ∧
        result (w 1)=X3CEncoding.codec.encode (X3CEncoding.normalizedInput input) := by
  have pushing := pushBit_executes (w 1) true store
  rw [status] at pushing
  let flagged := Function.update store (w 1) [true]
  have copying := copy_executes (extra+61) (w 51) (w 0) (w 63)
    (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) flagged
    (by simp [flagged,w.injective.eq_iff,empty 63 (by simp [MatchingMachine.generatorScratch])])
  have b : flagged (w 51)=X3CEncoding.codec.encode input := by simp [flagged,w.injective.eq_iff,backup]
  have s : flagged (w 0)=[] := by simp [flagged,w.injective.eq_iff,source]
  rw [b,s,List.append_nil] at copying
  let restored := Function.update flagged (w 0) (X3CEncoding.codec.encode input)
  have preparedEmpty (i : Fin 64) (member : i∈MatchingMachine.generatorScratch) : restored (w i)=[] := by
    have a : i≠0 := by intro equal;subst i;simp [MatchingMachine.generatorScratch] at member
    have b : i≠1 := by intro equal;subst i;simp [MatchingMachine.generatorScratch] at member
    simp [restored,flagged,w.injective.eq_iff,a,b,empty i member]
  obtain ⟨time,bound,running⟩ := generator_executes extra w restored (CoverInputValidation.inputRaw input) true
    (by simp [restored,CoverInputValidation.inputRaw_encode])
    (by simp [restored,flagged,w.injective.eq_iff,population,(CoverInputValidation.inputRaw_sizes input).1])
    (by simp [restored,flagged,w.injective.eq_iff]) preparedEmpty
  have typedBound : time ≤ typedGeneratorCost input := by
    simpa [restored,typedGeneratorCost] using bound
  refine ⟨1+1+(5*(X3CEncoding.codec.encode input).length+2+1+time),by omega,_,
    pushing.sequence (copying.sequence running),?_⟩
  rw [generatorResult_output,normalizedRaw_encoded]

end Counting.External.CoverNormalization
