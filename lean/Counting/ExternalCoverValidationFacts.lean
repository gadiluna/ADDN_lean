import Counting.ExternalCoverValidationPrepare
import Counting.ExternalCoverWitness

namespace Counting.External.CoverVerification
open MatchingMachine
set_option backward.isDefEq.respectTransparency false

def validationCanonical (w : VerifierWorkspace extra) (store : Fin (extra+64) → List Bool)
    (input : X3CEncoding.Input) :=
  Function.update (Function.update (Function.update (Function.update (Function.update store
    (w 51) (store (w 0))) (w 17) (List.replicate (3*input.1) true))
    (w 25) (List.replicate input.2.1 true)) (w 0) []) (w 1)
      [decide ((store (w 33)).length=input.2.1)]

theorem validated_canonical (extra : Nat) (w : VerifierWorkspace extra)
    (store : Fin (extra+64) → List Bool) (input : X3CEncoding.Input)
    (source : store (w 0)=X3CEncoding.codec.encode input) :
    validatedInput extra w store=
      Function.update (Function.update (Function.update (Function.update (savedInput w store)
        (w 17) (List.replicate (3*input.1) true)) (w 25) (List.replicate input.2.1 true)) (w 0) []) (w 1) [true] := by
  exact CoverInputValidation.result_canonical (extra+32) (validationRoles w) (savedInput w store) input
    (by simp [validationRoles,GeneratorWorkspace.literal,LiteralWorkspace.reader,literalPositions,savedInput,w.injective.eq_iff,source])

theorem validationFlag_canonical (extra : Nat) (w : VerifierWorkspace extra)
    (store : Fin (extra+64) → List Bool) (input : X3CEncoding.Input)
    (source : store (w 0)=X3CEncoding.codec.encode input) :
    validationFlag extra w store=decide ((store (w 33)).length=input.2.1) := by
  have valid := (CoverInputValidation.validInput_iff (store (w 0))).mpr ⟨input,source.symm⟩
  simp only [validationFlag,valid,Bool.true_and,validated_canonical extra w store input source]
  simp [w.injective.eq_iff]

theorem validationPrepared_canonical (extra : Nat) (w : VerifierWorkspace extra)
    (store : Fin (extra+64) → List Bool) (input : X3CEncoding.Input)
    (source : store (w 0)=X3CEncoding.codec.encode input) :
    validationPrepared extra w store=validationCanonical w store input := by
  rw [validationPrepared,validated_canonical extra w store input source,validationFlag_canonical extra w store input source]
  unfold validationCanonical savedInput
  funext r
  by_cases e1 : r=w 1
  · subst r;simp
  · simp [Function.update_apply,e1]

theorem validationFlag_iff (extra : Nat) (w : VerifierWorkspace extra) (store : Fin (extra+64) → List Bool) :
    validationFlag extra w store=true ↔ ∃ input : X3CEncoding.Input,
      X3CEncoding.codec.encode input=store (w 0) ∧ (store (w 33)).length=input.2.1 := by
  constructor
  · intro flag
    have both : CoverInputValidation.validInput (store (w 0))=true ∧
        decide ((store (w 33)).length=(validatedInput extra w store (w 25)).length)=true := by
      simpa only [validationFlag,Bool.and_eq_true] using flag
    have valid := both.1
    obtain ⟨input,encoded⟩ := (CoverInputValidation.validInput_iff _).mp valid
    rw [validationFlag_canonical extra w store input encoded.symm] at flag
    exact ⟨input,encoded,of_decide_eq_true flag⟩
  · rintro ⟨input,encoded,sized⟩
    rw [validationFlag_canonical extra w store input encoded.symm]
    exact decide_eq_true sized

theorem checkEncodedMask_implies_flag (extra : Nat) (w : VerifierWorkspace extra)
    (store : Fin (extra+64) → List Bool)
    (checked : checkEncodedMask (store (w 0)) (store (w 33))=true) :
    validationFlag extra w store=true := by
  cases decoded : X3CEncoding.codec.decodeExact (store (w 0)) with
  | none => simp [checkEncodedMask,decoded] at checked
  | some input =>
    have accepted : checkMask input (store (w 33))=true := by simpa [checkEncodedMask,decoded] using checked
    exact (validationFlag_iff extra w store).mpr ⟨input,
      (X3CEncoding.codec.decodeExact_iff _ _).mp decoded,((checkMask_iff _ _).mp accepted).1⟩

end Counting.External.CoverVerification
