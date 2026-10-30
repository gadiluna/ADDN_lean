import Counting.ExternalCNFEntryContinuation

namespace Counting.External.CNFMachine
open StackMachine StackMachine.Routine StackMachine.EncodingPrograms SATVerification
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option maxRecDepth 65536

def entryCost (input : List Bool) :=
  validateCoefficient*(input.length+1)^5+10*input.length+100+2*(CNFEncoding.codec.encode rejectFormula).length+
    match CNFEncoding.codec.decodeExact input with
    | none => 0
    | some formula => typedGeneratorCost formula

theorem entryRoutine_executes (extra : Nat) (w : ClauseWorkspace extra)
    (store : Fin (extra+52) → List Bool) (empty : ∀ i : Fin 52,i≠0 → store (w i)=[]) :
    ∃ time ≤ entryCost (store (w 0)),∃ result, Executes (entryRoutine extra w) store time result ∧
      result (w 1)=reduceThreeSAT (store (w 0)) := by
  let input := store (w 0)
  have saving := copy_executes (extra+49) (w 0) (w 46) (w 50)
    (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) store
    (empty 50 (by decide))
  rw [empty 46 (by decide),List.append_nil] at saving
  let saved := Function.update store (w 46) input
  have pushing := pushBit_executes (w 1) true saved
  have flagEmpty : saved (w 1)=[] := by simp [saved,w.injective.eq_iff,empty]
  rw [flagEmpty] at pushing
  let ready := Function.update saved (w 1) [true]
  have readySource : ready (w 0)=input := by simp [ready,saved,w.injective.eq_iff,input]
  have readyEmpty (i : Fin 32) (a : i≠0) (b : i≠1) : ready (entryValidationRoles extra w i)=[] := by
    fin_cases i <;> simp_all [entryValidationRoles,entryValidationPositions,ready,saved,w.injective.eq_iff]
  have readyFlag : ready (entryValidationRoles extra w 1)=[true] := by simp [entryValidationRoles,entryValidationPositions,ready]
  by_cases valid : validInput input=true
  · obtain ⟨formula,encoded⟩ := (validInput_iff input).mp valid
    have decoded : CNFEncoding.codec.decodeExact input=some formula :=
      (CNFEncoding.codec.decodeExact_iff input formula).mpr encoded
    obtain ⟨vt,vb,validation⟩ := validateRoutine_canonical (extra+20) (entryValidationRoles extra w) ready
      (CNFEncoding.toRaw formula) (by change ready (w 0)=_;rw [readySource,←encoded];rfl) readyFlag readyEmpty
    rw [validRaw_toRaw] at validation
    let checked := Function.update (Function.update (Function.update (Function.update (Function.update ready
      (w 17) (List.replicate formula.1 true)) (w 25) (List.replicate formula.2.length true))
      (w 47) (List.replicate formula.2.width true)) (w 0) []) (w 1) [true]
    have validationAs : Executes (validateRoutine (extra+20) (entryValidationRoles extra w)) ready vt checked := by
      simpa [entryValidationRoles,entryValidationPositions,CNFEncoding.toRaw,rawWidth_mapped,checked] using validation
    let consumed := Function.update checked (w 1) []
    have continuationEmpty (i : Fin 52) (member : i∈generatorScratch) : consumed (w i)=[] := by
      have a : i≠0 := by intro equal;subst i;simp [generatorScratch,formulaPrepareScratch,generatorClauseScratch] at member
      have b : i≠1 := by intro equal;subst i;simp [generatorScratch,formulaPrepareScratch,generatorClauseScratch] at member
      have c : i≠17 := by intro equal;subst i;simp [generatorScratch,formulaPrepareScratch,generatorClauseScratch] at member
      have d : i≠25 := by intro equal;subst i;simp [generatorScratch,formulaPrepareScratch,generatorClauseScratch] at member
      have e : i≠47 := by intro equal;subst i;simp [generatorScratch,formulaPrepareScratch,generatorClauseScratch] at member
      have f : i≠46 := by intro equal;subst i;simp [generatorScratch,formulaPrepareScratch,generatorClauseScratch] at member
      simp [consumed,checked,ready,saved,w.injective.eq_iff,a,b,c,d,e,f,empty i a]
    obtain ⟨acceptTime,acceptBound,result,accepting,output⟩ := acceptedContinuation_executes extra w consumed formula
      (by simp [consumed,checked,ready,saved,w.injective.eq_iff,encoded])
      (by simp [consumed,checked,w.injective.eq_iff]) (by simp [consumed])
      (by simp [consumed,checked,w.injective.eq_iff]) (by simp [consumed,checked,w.injective.eq_iff])
      (by simp [consumed,checked,w.injective.eq_iff]) continuationEmpty
    have branch := branch_executes_true (w 1) (acceptedContinuation extra w) (rejectedContinuation extra w)
      checked result [] acceptTime (by simp [checked]) accepting
    have combined := saving.sequence (pushing.sequence (validationAs.sequence branch))
    refine ⟨5*input.length+2+1+(1+1+(vt+1+(1+acceptTime))),?_,result,combined,?_⟩
    · change vt ≤ validateCoefficient*((ready (w 0)).length+1)^5 at vb
      rw [readySource] at vb
      rw [encoded] at acceptBound
      change _ ≤ entryCost input
      simp only [entryCost,decoded]
      omega
    · rw [output]
      change _=reduceThreeSAT input
      simp [reduceThreeSAT,decoded]
  · have validFalse : validInput input=false := Bool.eq_false_iff.mpr valid
    have decoded : CNFEncoding.codec.decodeExact input=none := by
      cases decode : CNFEncoding.codec.decodeExact input with
      | none => rfl
      | some formula =>
        have encoded := (CNFEncoding.codec.decodeExact_iff input formula).mp decode
        exact False.elim (valid ((validInput_iff input).mpr ⟨formula,encoded⟩))
    obtain ⟨vt,vb,checked,validation,flag,_measures⟩ := validateRoutine_executes (extra+20) (entryValidationRoles extra w)
      ready readyFlag readyEmpty
    have flagFalse : checked (w 1)=[false] := by
      change checked (w 1)=[validInput (ready (w 0))] at flag
      simpa only [readySource,validFalse] using flag
    let consumed := Function.update checked (w 1) []
    have rejecting := prepend_executes (w 1) (CNFEncoding.codec.encode rejectFormula) consumed
    have outputEmpty : consumed (w 1)=[] := by simp [consumed]
    rw [outputEmpty,List.append_nil] at rejecting
    have branch := branch_executes_false (w 1) (acceptedContinuation extra w) (rejectedContinuation extra w)
      checked _ [] _ flagFalse rejecting
    have combined := saving.sequence (pushing.sequence (validation.sequence branch))
    refine ⟨5*input.length+2+1+(1+1+(vt+1+(1+2*(CNFEncoding.codec.encode rejectFormula).length))),?_,_,combined,?_⟩
    · change vt ≤ validateCoefficient*((ready (w 0)).length+1)^5 at vb
      rw [readySource] at vb
      change _ ≤ entryCost input
      simp only [entryCost,decoded,Nat.add_zero]
      omega
    · simp only [Function.update_self]
      change _=reduceThreeSAT input
      simp [reduceThreeSAT,decoded]

end Counting.External.CNFMachine
