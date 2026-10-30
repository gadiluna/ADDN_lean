import Counting.ExternalMatchingClause

namespace Counting.External.MatchingMachine
open StackMachine StackMachine.Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

def clauseRows (first width shift occurrence : Nat) : List (List (Nat×Bool)) → List (List Nat)
  | [] => []
  | clause::rest => literalRows first width shift occurrence clause++clauseRows (first+1) width shift (occurrence+3) rest

def generateClauseLoop (extra : Nat) (w : LiteralWorkspace extra) : Routine (extra+46) :=
  forEach (w 23) (generateClause extra w)

def clauseLoopResult (extra : Nat) (w : LiteralWorkspace extra) (store : Fin (extra+48) → List Bool)
    (first width shift occurrence : Nat) (clauses : List (List (Nat×Bool))) (suffix : List Bool) :=
  Function.update (Function.update (Function.update (Function.update (Function.update store (w 0) suffix) (w 23) [])
    (w 34) (List.replicate (occurrence+3*clauses.length) true)) (w 35) (List.replicate clauses.length true++store (w 35)))
    (w 36) ((Encoding.sequence (Encoding.list Encoding.natural) (clauseRows first width shift occurrence clauses)).reverse++store (w 36))

theorem generateClauseLoop_executes (extra : Nat) (w : LiteralWorkspace extra)
    (clauses : List (List (Nat×Bool))) (n width shift bound first occurrence : Nat)
    (store : Fin (extra+48) → List Bool) (accepted : Bool) (suffix tail : List Bool)
    (source : store (w 0)=Encoding.sequence (Encoding.list (Encoding.product Encoding.natural Encoding.boolean)) clauses++suffix)
    (counter : store (w 23)=List.replicate clauses.length true)
    (status : store (w 1)=accepted::tail) (nValue : (store (w 17)).length=n)
    (widthValue : store (w 32)=List.replicate width true) (shiftValue : store (w 33)=List.replicate shift true)
    (occurrenceValue : store (w 34)=List.replicate occurrence true) (firstValue : (store (w 35)).length=first)
    (sourceBound : (store (w 0)).length ≤ bound) (hn : n ≤ bound) (hw : width ≤ bound) (hs : shift ≤ bound)
    (hf : first+clauses.length ≤ bound) (ho : occurrence+3*clauses.length ≤ bound)
    (three : ∀ clause∈clauses,clause.length=3)
    (fits : ∀ clause∈clauses,∀ literal∈clause,literal.1 ≤ n)
    (empty : ∀ i∈generateClauseScratch,store (w i)=[]) :
    ∃ time ≤ clauses.length*(26000*(bound+1)^4+2)+1,
      Executes (generateClauseLoop extra w) store time
        (clauseLoopResult extra w store first width shift occurrence clauses suffix) := by
  induction clauses generalizing store first occurrence with
  | nil =>
    obtain ⟨ran,halted⟩ := repeat_empty (w 23) (generateClause extra w) store counter
    have unchanged : clauseLoopResult extra w store first width shift occurrence [] suffix=store := by
      simp only [clauseLoopResult,clauseRows,Encoding.sequence,List.length_nil,Nat.mul_zero,Nat.add_zero,List.reverse_nil,List.nil_append,List.replicate_zero]
      have counterEmpty : store (w 23)=[] := counter
      have sourceEq : store (w 0)=suffix := source
      rw [←sourceEq,Function.update_eq_self,←counterEmpty,Function.update_eq_self,←occurrenceValue,Function.update_eq_self,Function.update_eq_self,Function.update_eq_self]
    exact ⟨1,by simp,⟨1,store⟩,ran,halted,unchanged.symm⟩
  | cons clause rest ih =>
    let consumed := Function.update store (w 23) (List.replicate rest.length true)
    let remaining := Encoding.sequence (Encoding.list (Encoding.product Encoding.natural Encoding.boolean)) rest++suffix
    have consumedSource : consumed (w 0)=(Encoding.list (Encoding.product Encoding.natural Encoding.boolean)).encode clause++remaining := by
      simpa [consumed,remaining,w.injective.eq_iff,Encoding.sequence,List.append_assoc] using source
    have consumedEmpty (i : Fin 48) (member : i∈generateClauseScratch) : consumed (w i)=[] := by
      have different : i≠23 := by intro same;subst i;simp [generateClauseScratch,generateLiteralScratch] at member
      simpa [consumed,w.injective.eq_iff,different] using empty i member
    have clauseThree : clause.length=3 := three clause (by simp)
    obtain ⟨bodyTime,bodyBound,bodyFinish,bodyRun,bodyHalt,bodyStore⟩ := generateClause_executes extra w clause n width shift first bound occurrence
      consumed accepted remaining tail clauseThree consumedSource
      (by simp [consumed,w.injective.eq_iff,status]) (by simpa [consumed,w.injective.eq_iff] using nValue)
      (by simp [consumed,w.injective.eq_iff,widthValue]) (by simp [consumed,w.injective.eq_iff,shiftValue])
      (by simp [consumed,w.injective.eq_iff,occurrenceValue]) (by simpa [consumed,w.injective.eq_iff] using firstValue)
      (by simpa [consumed,w.injective.eq_iff] using sourceBound) hn hw hs
      (by simp only [List.length_cons] at hf;omega) (by simp only [List.length_cons] at ho;omega)
      (fits clause (by simp)) consumedEmpty
    let next := matchingClauseResult extra w consumed first width shift occurrence clause remaining
    have nextSource : next (w 0)=Encoding.sequence (Encoding.list (Encoding.product Encoding.natural Encoding.boolean)) rest++suffix := by
      simp [next,matchingClauseResult,w.injective.eq_iff,remaining]
    have nextCounter : next (w 23)=List.replicate rest.length true := by simp [next,matchingClauseResult,consumed,w.injective.eq_iff]
    have nextStatus : next (w 1)=accepted::tail := by simp [next,matchingClauseResult,consumed,w.injective.eq_iff,status]
    have nextN : (next (w 17)).length=n := by simpa [next,matchingClauseResult,consumed,w.injective.eq_iff] using nValue
    have nextWidth : next (w 32)=List.replicate width true := by simp [next,matchingClauseResult,consumed,w.injective.eq_iff,widthValue]
    have nextShift : next (w 33)=List.replicate shift true := by simp [next,matchingClauseResult,consumed,w.injective.eq_iff,shiftValue]
    have nextOccurrence : next (w 34)=List.replicate (occurrence+3) true := by simp [next,matchingClauseResult,w.injective.eq_iff,clauseThree]
    have nextFirst : (next (w 35)).length=first+1 := by simp [next,matchingClauseResult,consumed,w.injective.eq_iff,firstValue]
    have nextBound : (next (w 0)).length ≤ bound := by
      rw [nextSource]
      rw [source] at sourceBound
      simp only [Encoding.sequence,List.length_append] at sourceBound ⊢
      omega
    have nextEmpty (i : Fin 48) (member : i∈generateClauseScratch) : next (w i)=[] := by
      have a : i≠0 := by intro same;subst i;simp [generateClauseScratch,generateLiteralScratch] at member
      have b : i≠34 := by intro same;subst i;simp [generateClauseScratch,generateLiteralScratch] at member
      have c : i≠35 := by intro same;subst i;simp [generateClauseScratch,generateLiteralScratch] at member
      have d : i≠36 := by intro same;subst i;simp [generateClauseScratch,generateLiteralScratch] at member
      simpa [next,matchingClauseResult,w.injective.eq_iff,a,b,c,d] using consumedEmpty i member
    obtain ⟨tailTime,tailBound,tailFinish,tailRun,tailHalt,tailStore⟩ := ih (first+1) (occurrence+3) next nextSource nextCounter nextStatus nextN nextWidth nextShift
      nextOccurrence nextFirst nextBound (by simp only [List.length_cons] at hf;omega)
      (by simp only [List.length_cons] at ho;omega)
      (fun cl member=>three cl (by simp [member])) (fun cl member=>fits cl (by simp [member])) nextEmpty
    have firstRun := repeat_iteration (w 23) (generateClause extra w) store true (List.replicate rest.length true)
      (by simpa only [List.length_cons,List.replicate_succ] using counter) bodyTime bodyFinish bodyRun bodyHalt
    change Machine.run (step (generateClauseLoop extra w).program) (bodyTime+2) ⟨0,store⟩=some ⟨0,bodyFinish.store⟩ at firstRun
    refine ⟨bodyTime+2+tailTime,?_,tailFinish,?_,tailHalt,?_⟩
    · simp only [List.length_cons];nlinarith only [bodyBound,tailBound]
    · rw [Machine.run_add,firstRun,Option.bind_some,bodyStore]
      exact tailRun
    · rw [tailStore]
      funext r
      by_cases a : r=w 0
      · subst r;simp [clauseLoopResult,w.injective.eq_iff]
      · by_cases c : r=w 23
        · subst r;simp [clauseLoopResult,w.injective.eq_iff]
        · by_cases b : r=w 34
          · subst r
            simp only [clauseLoopResult,Function.update_of_ne (w.injective.ne (by decide : (34:Fin 48)≠36)),
              Function.update_of_ne (w.injective.ne (by decide : (34:Fin 48)≠35)),Function.update_self,List.length_cons]
            congr 1
            omega
          · by_cases d : r=w 35
            · subst r
              simp [clauseLoopResult,next,matchingClauseResult,consumed,w.injective.eq_iff,List.replicate_succ,replicate_append_cons]
            · by_cases o : r=w 36
              · subst r
                simp [clauseLoopResult,clauseRows,next,matchingClauseResult,consumed,w.injective.eq_iff,
                  sequence_append,List.reverse_append,List.append_assoc]
              · simp [clauseLoopResult,next,matchingClauseResult,consumed,a,c,b,d,o]

end Counting.External.MatchingMachine
