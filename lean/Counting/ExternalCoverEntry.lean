import Counting.ExternalCoverContinuation
import Counting.ExternalMatchingInputValidation

namespace Counting.External.CoverMachine
open StackMachine StackMachine.Routine StackMachine.EncodingPrograms SATVerification MatchingMachine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option maxRecDepth 65536

def entryValidationPositions : Fin 32 ↪ Fin 64 :=
  ⟨fun i=>i.castLE (by decide),by intro i j same;exact Fin.ext (congrArg (fun x : Fin 64=>x.val) same)⟩
def entryValidationRoles (extra : Nat) (w : GeneratorWorkspace extra) : SATWorkspace (extra+32) :=
  entryValidationPositions.trans w

def entryRoutine (extra : Nat) (w : GeneratorWorkspace extra) : Routine (extra+62) :=
  sequence (ofProgram (ListPrograms.copyProgram (extra+61) (w 0) (w 51) (w 63)))
    (sequence (pushBit (w 1) true)
      (sequence (MatchingInputValidation.routine (extra+32) (entryValidationRoles extra w))
        (branchRoutine (w 1) (acceptedContinuation extra w) (rejectedContinuation extra w))))

def entryCost (input : List Bool) :=
  MatchingInputValidation.coefficient*(input.length+1)^5+10*input.length+100+
    2*(X3CEncoding.codec.encode rejectCover).length+
    if MatchingInputValidation.validInput input then
      match ThreeDMEncoding.codec.decodeExact input with
      | none => 0
      | some formula => typedGeneratorCost formula
    else 0

theorem reduceCover_rejected (input : List Bool) (invalid : MatchingInputValidation.validInput input=false) :
    reduceCover input=X3CEncoding.codec.encode rejectCover := by
  cases decoded : ThreeDMEncoding.codec.decodeExact input with
  | none => simp [reduceCover,decoded]
  | some formula =>
    have encoded := (ThreeDMEncoding.codec.decodeExact_iff input formula).mp decoded
    have valid := (MatchingInputValidation.validInput_iff input).mpr ⟨formula,encoded⟩
    rw [invalid] at valid
    contradiction

/-- A total generating transducer: malformed matching sources map
to a fixed negative exact-cover instance; accepted sources run the real
coordinate-shifting generator on the restored original encoding. -/
theorem entryRoutine_executes (extra : Nat) (w : GeneratorWorkspace extra)
    (store : Fin (extra+64) → List Bool) (empty : ∀ i : Fin 64,i≠0 → store (w i)=[]) :
    ∃ time ≤ entryCost (store (w 0)),∃ result,
      Executes (entryRoutine extra w) store time result ∧ result (w 1)=reduceCover (store (w 0)) := by
  let input := store (w 0)
  have saving := copy_executes (extra+61) (w 0) (w 51) (w 63)
    (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) store
    (empty 63 (by decide))
  rw [empty 51 (by decide),List.append_nil] at saving
  let saved := Function.update store (w 51) input
  have pushing := pushBit_executes (w 1) true saved
  have flagEmpty : saved (w 1)=[] := by simp [saved,w.injective.eq_iff,empty]
  rw [flagEmpty] at pushing
  let ready := Function.update saved (w 1) [true]
  have readySource : ready (w 0)=input := by simp [ready,saved,w.injective.eq_iff,input]
  have readyEmpty (i : Fin 32) (a : i≠0) (b : i≠1) : ready (entryValidationRoles extra w i)=[] := by
    fin_cases i <;> simp_all [entryValidationRoles,entryValidationPositions,ready,saved,w.injective.eq_iff]
  have readyFlag : ready (entryValidationRoles extra w 1)=[true] := by
    simp [entryValidationRoles,entryValidationPositions,ready]
  obtain ⟨validateTime,validateBound,validation⟩ := MatchingInputValidation.routine_executes (extra+32)
    (entryValidationRoles extra w) ready readyFlag readyEmpty
  have validateLimit : validateTime ≤ MatchingInputValidation.coefficient*(input.length+1)^5 := by
    change validateTime ≤ MatchingInputValidation.coefficient*((ready (w 0)).length+1)^5 at validateBound
    simpa only [readySource] using validateBound
  by_cases valid : MatchingInputValidation.validInput input=true
  · obtain ⟨formula,encoded⟩ := (MatchingInputValidation.validInput_iff input).mp valid
    have decoded : ThreeDMEncoding.codec.decodeExact input=some formula :=
      (ThreeDMEncoding.codec.decodeExact_iff input formula).mpr encoded
    have canonicalSource : ready (entryValidationRoles extra w 0)=ThreeDMEncoding.codec.encode formula := by
      change ready (w 0)=_
      rw [readySource,encoded]
    rw [MatchingInputValidation.result_canonical (extra+32) (entryValidationRoles extra w) ready formula canonicalSource] at validation
    let checked := Function.update (Function.update (Function.update (Function.update ready
      (w 17) (List.replicate formula.1 true)) (w 25) (List.replicate formula.2.1 true)) (w 0) []) (w 1) [true]
    have validationAs : Executes (MatchingInputValidation.routine (extra+32) (entryValidationRoles extra w)) ready validateTime checked := by
      simpa [entryValidationRoles,entryValidationPositions,checked] using validation
    let consumed := Function.update checked (w 1) []
    have continuationEmpty (i : Fin 64) (member : i∈generatorScratch) : consumed (w i)=[] := by
      have a : i≠0 := by intro equal;subst i;simp [generatorScratch] at member
      have b : i≠1 := by intro equal;subst i;simp [generatorScratch] at member
      have c : i≠17 := by intro equal;subst i;simp [generatorScratch] at member
      have d : i≠25 := by intro equal;subst i;simp [generatorScratch] at member
      have f : i≠51 := by intro equal;subst i;simp [generatorScratch] at member
      simp [consumed,checked,ready,saved,w.injective.eq_iff,a,b,c,d,f,empty i a]
    obtain ⟨acceptTime,acceptBound,result,accepting,output⟩ := acceptedContinuation_executes extra w consumed formula
      (by simp [consumed,checked,ready,saved,w.injective.eq_iff,encoded])
      (by simp [consumed,checked,w.injective.eq_iff]) (by simp [consumed])
      (by simp [consumed,checked,w.injective.eq_iff]) (by simp [consumed,checked,w.injective.eq_iff]) continuationEmpty
    have branch := branch_executes_true (w 1) (acceptedContinuation extra w) (rejectedContinuation extra w)
      checked result [] acceptTime (by simp [checked]) accepting
    have combined := saving.sequence (pushing.sequence (validationAs.sequence branch))
    refine ⟨5*input.length+2+1+(1+1+(validateTime+1+(1+acceptTime))),?_,result,combined,?_⟩
    · rw [encoded] at acceptBound
      change _ ≤ entryCost input
      simp only [entryCost,valid,if_true,decoded]
      omega
    · rw [output]
      change _=reduceCover input
      rw [←encoded,reduceCover_encoded formula]
  · have invalid : MatchingInputValidation.validInput input=false := Bool.eq_false_iff.mpr valid
    let checked := MatchingInputValidation.result (extra+32) (entryValidationRoles extra w) ready
    have flagFalse : checked (w 1)=[false] := by
      have flag := MatchingInputValidation.result_flag (extra+32) (entryValidationRoles extra w) ready
      change checked (w 1)=[MatchingInputValidation.validInput (ready (w 0))] at flag
      simpa only [readySource,invalid] using flag
    let consumed := Function.update checked (w 1) []
    have rejecting := prepend_executes (w 1) (X3CEncoding.codec.encode rejectCover) consumed
    have outputEmpty : consumed (w 1)=[] := by simp [consumed]
    rw [outputEmpty,List.append_nil] at rejecting
    have branch := branch_executes_false (w 1) (acceptedContinuation extra w) (rejectedContinuation extra w)
      checked _ [] _ flagFalse rejecting
    have combined := saving.sequence (pushing.sequence (validation.sequence branch))
    refine ⟨5*input.length+2+1+(1+1+(validateTime+1+(1+2*(X3CEncoding.codec.encode rejectCover).length))),?_,_,combined,?_⟩
    · change _ ≤ entryCost input
      simp only [entryCost,invalid,Bool.false_eq_true,if_false,Nat.add_zero]
      omega
    · simp only [Function.update_self]
      exact (reduceCover_rejected input invalid).symm

end Counting.External.CoverMachine
