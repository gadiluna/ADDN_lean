import Counting.ExternalCoverInputValidation
import Counting.ExternalCoverWitnessLength

namespace Counting.External.CoverVerification
open StackMachine StackMachine.Routine StackMachine.EncodingPrograms MatchingMachine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

def validationRoles (w : VerifierWorkspace extra) : SATVerification.SATWorkspace (extra+32) := w.literal.reader

def savedInput (w : VerifierWorkspace extra) (store : Fin (extra+64) → List Bool) :=
  Function.update (Function.update store (w 51) (store (w 0))) (w 1) [true]

def validatedInput (extra : Nat) (w : VerifierWorkspace extra) (store : Fin (extra+64) → List Bool) :=
  CoverInputValidation.result (extra+32) (validationRoles w) (savedInput w store)

def validationFlag (extra : Nat) (w : VerifierWorkspace extra) (store : Fin (extra+64) → List Bool) :=
  CoverInputValidation.validInput (store (w 0)) &&
    decide ((store (w 33)).length=(validatedInput extra w store (w 25)).length)

def validationPrepared (extra : Nat) (w : VerifierWorkspace extra) (store : Fin (extra+64) → List Bool) :=
  Function.update (validatedInput extra w store) (w 1) [validationFlag extra w store]

def validationPrepare (extra : Nat) (w : VerifierWorkspace extra) : Routine (extra+62) :=
  sequence (ofProgram (ListPrograms.copyProgram (extra+61) (w 0) (w 51) (w 63)))
    (sequence (pushBit (w 1) true)
      (sequence (CoverInputValidation.routine (extra+32) (validationRoles w)) (witnessLength extra w)))

theorem validated_unary (extra : Nat) (w : VerifierWorkspace extra) (store : Fin (extra+64) → List Bool)
    (empty : store (w 25)=[]) :
    validatedInput extra w store (w 25)=List.replicate (validatedInput extra w store (w 25)).length true := by
  unfold validatedInput
  cases decoded : MatchingVerification.rawCodec.decodeExact (savedInput w store (validationRoles w 0)) with
  | none =>
    simp only [CoverInputValidation.result,decoded]
    simp [validationRoles,GeneratorWorkspace.literal,LiteralWorkspace.reader,
      literalPositions,savedInput,w.injective.eq_iff,empty]
  | some raw =>
    simp only [CoverInputValidation.result,decoded]
    simp [CoverInputValidation.measured,validationRoles,GeneratorWorkspace.literal,LiteralWorkspace.reader,
      literalPositions,w.injective.eq_iff]

theorem validated_count_bound (extra : Nat) (w : VerifierWorkspace extra) (store : Fin (extra+64) → List Bool)
    (empty : store (w 25)=[]) :
    (validatedInput extra w store (w 25)).length ≤ (store (w 0)).length := by
  unfold validatedInput
  cases decoded : MatchingVerification.rawCodec.decodeExact (savedInput w store (validationRoles w 0)) with
  | none =>
    simp only [CoverInputValidation.result,decoded]
    simp [validationRoles,GeneratorWorkspace.literal,LiteralWorkspace.reader,literalPositions,
      savedInput,w.injective.eq_iff,empty]
  | some raw =>
    have encoded := (MatchingVerification.rawCodec.decodeExact_iff _ raw).mp decoded
    have source : savedInput w store (validationRoles w 0)=store (w 0) := by
      simp [validationRoles,GeneratorWorkspace.literal,LiteralWorkspace.reader,literalPositions,
        savedInput,w.injective.eq_iff]
    rw [source] at encoded
    have count := VerifiedParser.sequence_count_le (codec:=MatchingVerification.clauseCodec)
      (by intro row;rw [MatchingVerification.clause_encode,Encoding.list_length];omega) raw.2
    have length : (MatchingVerification.rawCodec.encode raw).length=
        ((Encoding.list Encoding.boolean).encode raw.1).length+(Encoding.natural.encode raw.2.length).length+
          (Encoding.sequence MatchingVerification.clauseCodec raw.2).length := by
      simp only [MatchingVerification.rawCodec,Encoding.product,Encoding.list,List.length_append]
      omega
    have bound : raw.2.length ≤ (store (w 0)).length := by rw [←encoded,length];omega
    simp only [CoverInputValidation.result,decoded]
    simpa [CoverInputValidation.measured,validationRoles,
      GeneratorWorkspace.literal,LiteralWorkspace.reader,literalPositions,w.injective.eq_iff] using bound

def validationCoefficient := CoverInputValidation.coefficient+40

theorem validationPrepare_executes (extra : Nat) (w : VerifierWorkspace extra)
    (store : Fin (extra+64) → List Bool)
    (empty : ∀ i : Fin 64,i≠0 → i≠33 → store (w i)=[]) :
    ∃ time ≤ validationCoefficient*((store (w 0)).length+(store (w 33)).length+1)^5,
      Executes (validationPrepare extra w) store time (validationPrepared extra w store) := by
  have copying := copy_executes (extra+61) (w 0) (w 51) (w 63)
    (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) store (empty 63 (by decide) (by decide))
  rw [empty 51 (by decide) (by decide),List.append_nil] at copying
  let copied := Function.update store (w 51) (store (w 0))
  have pushing : Executes (pushBit (w 1) true) copied 1 (savedInput w store) := by
    simpa [copied,savedInput,w.injective.eq_iff,empty] using pushBit_executes (w 1) true copied
  have validatorEmpty (i : Fin 32) (n0 : i≠0) (n1 : i≠1) : savedInput w store (validationRoles w i)=[] := by
    have a : (⟨i.val,by omega⟩:Fin 64)≠0 := by intro same;apply n0;exact Fin.ext (congrArg (fun j : Fin 64=>j.val) same)
    have b : (⟨i.val,by omega⟩:Fin 64)≠33 := by intro same;have value:=congrArg (fun j : Fin 64=>j.val) same;norm_num at value;omega
    have c : (⟨i.val,by omega⟩:Fin 64)≠1 := by intro same;apply n1;exact Fin.ext (congrArg (fun j : Fin 64=>j.val) same)
    have d : (⟨i.val,by omega⟩:Fin 64)≠51 := by intro same;have value:=congrArg (fun j : Fin 64=>j.val) same;norm_num at value;omega
    simpa [validationRoles,GeneratorWorkspace.literal,LiteralWorkspace.reader,literalPositions,
      savedInput,w.injective.eq_iff,c,d] using empty ⟨i.val,by omega⟩ a b
  obtain ⟨validateTime,validateBound,validating⟩ := CoverInputValidation.routine_executes (extra+32) (validationRoles w) (savedInput w store)
    (by simp [validationRoles,GeneratorWorkspace.literal,LiteralWorkspace.reader,literalPositions,
      savedInput]) validatorEmpty
  have status : validatedInput extra w store (w 1)=[CoverInputValidation.validInput (store (w 0))] := by
    have result := CoverInputValidation.result_flag (extra+32) (validationRoles w) (savedInput w store)
    simpa [validatedInput,validationRoles,GeneratorWorkspace.literal,LiteralWorkspace.reader,literalPositions,
      savedInput,w.injective.eq_iff] using result
  have outside (i : Fin 64) (large : 32 ≤ i.val) : validatedInput extra w store (w i)=savedInput w store (w i) := by
    unfold validatedInput
    cases decoded : MatchingVerification.rawCodec.decodeExact (savedInput w store (validationRoles w 0)) with
    | none =>
      simp only [CoverInputValidation.result,decoded]
      simp [validationRoles,GeneratorWorkspace.literal,LiteralWorkspace.reader,literalPositions,w.injective.eq_iff,
        show i≠1 by intro h;subst i;omega]
    | some raw =>
      simp only [CoverInputValidation.result,decoded]
      simp [CoverInputValidation.measured,validationRoles,GeneratorWorkspace.literal,LiteralWorkspace.reader,
        literalPositions,w.injective.eq_iff,show i≠0 by intro h;subst i;omega,
        show i≠1 by intro h;subst i;omega,show i≠17 by intro h;subst i;omega,show i≠25 by intro h;subst i;omega]
  have scratch (i : Fin 64) (member : i∈([43,44,45]:List (Fin 64))) : validatedInput extra w store (w i)=[] := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl
    all_goals rw [outside _ (by decide)];simp [savedInput,w.injective.eq_iff,empty]
  obtain ⟨lengthTime,lengthBound,measuring⟩ := witnessLength_executes extra w (validatedInput extra w store)
    (CoverInputValidation.validInput (store (w 0))) [] status
    (validated_unary extra w store (empty 25 (by decide) (by decide))) scratch
  have maskSame : validatedInput extra w store (w 33)=store (w 33) := by
    rw [outside 33 (by decide)];simp [savedInput,w.injective.eq_iff]
  rw [maskSame] at measuring lengthBound
  change Executes (witnessLength extra w) (validatedInput extra w store) lengthTime (validationPrepared extra w store) at measuring
  refine ⟨5*(store (w 0)).length+2+1+(1+1+(validateTime+1+lengthTime)),?_,copying.sequence (pushing.sequence (validating.sequence measuring))⟩
  have countBound := validated_count_bound extra w store (empty 25 (by decide) (by decide))
  have sourceAt : savedInput w store (validationRoles w 0)=store (w 0) := by
    simp [validationRoles,GeneratorWorkspace.literal,LiteralWorkspace.reader,literalPositions,savedInput,w.injective.eq_iff]
  rw [sourceAt] at validateBound
  let size := (store (w 0)).length+(store (w 33)).length+1
  have validateLimit : validateTime ≤ CoverInputValidation.coefficient*size^5 :=
    validateBound.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by dsimp [size];omega) _))
  have linear : size ≤ size^5 := Nat.le_self_pow (by decide) _
  change _ ≤ validationCoefficient*size^5
  unfold validationCoefficient
  dsimp only [size] at *
  nlinarith only [validateLimit,lengthBound,countBound,linear]

end Counting.External.CoverVerification
