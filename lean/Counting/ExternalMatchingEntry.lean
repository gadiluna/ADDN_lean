import Counting.ExternalMatchingEntryContinuation

namespace Counting.External.MatchingMachine
open StackMachine StackMachine.Routine StackMachine.EncodingPrograms SATVerification
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option maxRecDepth 65536

def entryCost (input : List Bool) :=
  MatchingValidation.coefficient*(input.length+1)^5+10*input.length+100+
    2*(ThreeDMEncoding.codec.encode rejectMatching).length+
    if MatchingValidation.check input then
      match CNFEncoding.codec.decodeExact input with
      | none => 0
      | some formula => typedGeneratorCost formula
    else 0

theorem reduceMatching_rejected (input : List Bool) (invalid : MatchingValidation.check input=false) :
    reduceMatching input=ThreeDMEncoding.codec.encode rejectMatching := by
  cases decoded : CNFEncoding.codec.decodeExact input with
  | none => simp [reduceMatching,decoded]
  | some formula =>
    have encoded := (CNFEncoding.codec.decodeExact_iff input formula).mp decoded
    have notThree : ¬∀ clause∈formula.2,clause.length=3 := by
      intro three
      have valid := (MatchingValidation.check_iff input).mpr ⟨formula,encoded,three⟩
      rw [invalid] at valid
      cases valid
    simp [reduceMatching,decoded,notThree]

/-- A total generating transducer: malformed or non-three-CNF sources map
to the fixed negative matching instance; accepted sources run the real
sparse generator on the restored original encoding. -/
theorem entryRoutine_executes (extra : Nat) (w : GeneratorWorkspace extra)
    (store : Fin (extra+64) → List Bool) (empty : ∀ i : Fin 64,i≠0 → store (w i)=[]) :
    ∃ time ≤ entryCost (store (w 0)),∃ result,
      Executes (entryRoutine extra w) store time result ∧ result (w 1)=reduceMatching (store (w 0)) := by
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
  obtain ⟨validateTime,validateBound,validation⟩ := MatchingValidation.routine_executes (extra+32)
    (entryValidationRoles extra w) ready readyFlag readyEmpty
  have validateLimit : validateTime ≤ MatchingValidation.coefficient*(input.length+1)^5 := by
    change validateTime ≤ MatchingValidation.coefficient*((ready (w 0)).length+1)^5 at validateBound
    simpa only [readySource] using validateBound
  by_cases valid : MatchingValidation.check input=true
  · obtain ⟨formula,encoded,three⟩ := (MatchingValidation.check_iff input).mp valid
    have decoded : CNFEncoding.codec.decodeExact input=some formula :=
      (CNFEncoding.codec.decodeExact_iff input formula).mpr encoded
    have canonicalSource : ready (entryValidationRoles extra w 0)=CNFEncoding.codec.encode formula := by
      change ready (w 0)=_
      rw [readySource,encoded]
    rw [MatchingValidation.result_canonical (extra+32) (entryValidationRoles extra w) ready formula canonicalSource three] at validation
    simp only [MatchingValidation.measured,validRaw_toRaw] at validation
    let checked := Function.update (Function.update (Function.update (Function.update (Function.update ready
      (w 17) (List.replicate formula.1 true)) (w 25) (List.replicate formula.2.length true))
      (w 31) (List.replicate (CNFMachine.rawWidth (CNFEncoding.toRaw formula).2) true)) (w 0) []) (w 1) [true]
    have validationAs : Executes (MatchingValidation.routine (extra+32) (entryValidationRoles extra w)) ready validateTime checked := by
      simpa [entryValidationRoles,entryValidationPositions,CNFEncoding.toRaw,checked] using validation
    let consumed := Function.update checked (w 1) []
    have continuationEmpty (i : Fin 64) (member : i∈generatorScratch) : consumed (w i)=[] := by
      have a : i≠0 := by intro equal;subst i;simp [generatorScratch] at member
      have b : i≠1 := by intro equal;subst i;simp [generatorScratch] at member
      have c : i≠17 := by intro equal;subst i;simp [generatorScratch] at member
      have d : i≠25 := by intro equal;subst i;simp [generatorScratch] at member
      have e : i≠31 := by intro equal;subst i;simp [generatorScratch] at member
      have f : i≠51 := by intro equal;subst i;simp [generatorScratch] at member
      simp [consumed,checked,ready,saved,w.injective.eq_iff,a,b,c,d,e,f,empty i a]
    obtain ⟨acceptTime,acceptBound,result,accepting,output⟩ := acceptedContinuation_executes extra w consumed formula three
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
      change _=reduceMatching input
      rw [←encoded,reduceMatching_encoded formula three]
  · have invalid : MatchingValidation.check input=false := Bool.eq_false_iff.mpr valid
    let checked := MatchingValidation.result (extra+32) (entryValidationRoles extra w) ready
    have flagFalse : checked (w 1)=[false] := by
      have flag := MatchingValidation.result_flag (extra+32) (entryValidationRoles extra w) ready
      change checked (w 1)=[MatchingValidation.check (ready (w 0))] at flag
      simpa only [readySource,invalid] using flag
    let consumed := Function.update checked (w 1) []
    have rejecting := prepend_executes (w 1) (ThreeDMEncoding.codec.encode rejectMatching) consumed
    have outputEmpty : consumed (w 1)=[] := by simp [consumed]
    rw [outputEmpty,List.append_nil] at rejecting
    have branch := branch_executes_false (w 1) (acceptedContinuation extra w) (rejectedContinuation extra w)
      checked _ [] _ flagFalse rejecting
    have combined := saving.sequence (pushing.sequence (validation.sequence branch))
    refine ⟨5*input.length+2+1+(1+1+(validateTime+1+(1+2*(ThreeDMEncoding.codec.encode rejectMatching).length))),?_,_,combined,?_⟩
    · change _ ≤ entryCost input
      simp only [entryCost,invalid,Bool.false_eq_true,if_false,Nat.add_zero]
      omega
    · simp only [Function.update_self]
      exact (reduceMatching_rejected input invalid).symm

end Counting.External.MatchingMachine
