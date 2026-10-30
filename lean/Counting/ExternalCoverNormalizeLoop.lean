import Counting.ExternalCoverNormalizeStep
import Counting.ExternalCoverNormalizeSpec

namespace Counting.External.CoverNormalization
open StackMachine StackMachine.Routine CoverMachine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

def dedupRows (extra : Nat) (w : RowWorkspace extra) : Routine (extra+46) :=
  forEach (w 23) (rowStep extra w)

def dedupResult (w : RowWorkspace extra) (store : Fin (extra+48) → List Bool)
    (before rows : List MatchingVerification.RawClause) (suffix : List Bool) :=
  Function.update (Function.update (Function.update (Function.update (Function.update store
    (w 0) suffix) (w 23) []) (w 36)
      ((Encoding.sequence MatchingVerification.clauseCodec (freshRows before rows)).reverse++store (w 36)))
    (w 41) (List.replicate (freshRows before rows).length true++store (w 41)))
    (w 40) (List.replicate rows.length true++store (w 40))

theorem unaryPrefix_push (n : Nat) (tail : List Bool) :
    List.replicate n true++true::tail=true::(List.replicate n true++tail) := by
  rw [←List.singleton_append,←List.append_assoc,←List.replicate_succ',List.replicate_succ,
    List.cons_append]

/-- Every comparison, retained-row copy, counter increment and scratch cleanup
is executed by the loop. The preserved original table is rescanned only up to
the visited-row counter, so later equal rows never suppress a first occurrence. -/
theorem dedupRows_executes (extra : Nat) (w : RowWorkspace extra)
    (before rows : List MatchingVerification.RawClause) (bound : Nat)
    (store : Fin (extra+48) → List Bool) (accepted : Bool) (tail suffix : List Bool)
    (source : store (w 0)=Encoding.sequence MatchingVerification.clauseCodec rows++suffix)
    (table : store (w 39)=Encoding.sequence MatchingVerification.clauseCodec (before++rows))
    (counter : store (w 23)=List.replicate rows.length true)
    (visited : store (w 40)=List.replicate before.length true)
    (status : store (w 1)=accepted::tail)
    (sizeBound : (store (w 0)).length+(store (w 39)).length+1 ≤ bound)
    (empty : ∀ i∈stepScratch,store (w i)=[]) :
    ∃ time ≤ rows.length*(2000*bound^2+2)+1,
      Executes (dedupRows extra w) store time (dedupResult w store before rows suffix) := by
  induction rows generalizing before store with
  | nil =>
    obtain ⟨ran,halted⟩ := repeat_empty (w 23) (rowStep extra w) store counter
    have unchanged : dedupResult w store before [] suffix=store := by
      simp only [dedupResult,freshRows,Encoding.sequence,List.reverse_nil,List.nil_append,
        List.length_nil,List.replicate_zero]
      have sourceEq : store (w 0)=suffix := source
      have counterEq : store (w 23)=[] := counter
      rw [←sourceEq,Function.update_eq_self,←counterEq,Function.update_eq_self]
      simp only [Function.update_eq_self]
    exact ⟨1,by simp,⟨1,store⟩,ran,halted,unchanged.symm⟩
  | cons row rest ih =>
    let consumed := Function.update store (w 23) (List.replicate rest.length true)
    let remaining := Encoding.sequence MatchingVerification.clauseCodec rest++suffix
    have consumedSource : consumed (w 0)=MatchingVerification.clauseCodec.encode row++remaining := by
      simpa [consumed,remaining,w.injective.eq_iff,Encoding.sequence,List.append_assoc] using source
    have consumedEmpty (i : Fin 48) (member : i∈stepScratch) : consumed (w i)=[] := by
      have different : i≠23 := by intro same;subst i;simp [stepScratch,previousScratch,matchScratch] at member
      simpa [consumed,w.injective.eq_iff,different] using empty i member
    obtain ⟨bodyTime,bodyBound,bodyFinish,bodyRun,bodyHalt,bodyStore⟩ := rowStep_executes extra w
      row before rest consumed accepted tail remaining consumedSource
      (by simp [consumed,w.injective.eq_iff,table])
      (by simp [consumed,w.injective.eq_iff,visited])
      (by simp [consumed,w.injective.eq_iff,status]) consumedEmpty
    let next := stepResult w consumed row before remaining
    have bodyResult : bodyFinish.store=next := bodyStore
    have nextSource : next (w 0)=Encoding.sequence MatchingVerification.clauseCodec rest++suffix := by
      simp [next,stepResult,w.injective.eq_iff,remaining]
    have nextTable : next (w 39)=Encoding.sequence MatchingVerification.clauseCodec ((before++[row])++rest) := by
      simp [next,stepResult,consumed,w.injective.eq_iff,table,List.append_assoc]
    have nextCounter : next (w 23)=List.replicate rest.length true := by
      simp [next,stepResult,consumed,w.injective.eq_iff]
    have nextVisited : next (w 40)=List.replicate (before++[row]).length true := by
      simp [next,stepResult,consumed,w.injective.eq_iff,visited,List.replicate_succ]
    have nextStatus : next (w 1)=accepted::tail := by
      simp [next,stepResult,consumed,w.injective.eq_iff,status]
    have tableSame : next (w 39)=store (w 39) := by
      simp [next,stepResult,consumed,w.injective.eq_iff]
    have nextBound : (next (w 0)).length+(next (w 39)).length+1 ≤ bound := by
      rw [nextSource,tableSame]
      rw [source] at sizeBound
      simp only [Encoding.sequence,List.length_append] at sizeBound ⊢
      omega
    have nextEmpty (i : Fin 48) (member : i∈stepScratch) : next (w i)=[] := by
      have a : i≠0 := by intro same;subst i;simp [stepScratch,previousScratch,matchScratch] at member
      have b : i≠36 := by intro same;subst i;simp [stepScratch,previousScratch,matchScratch] at member
      have c : i≠41 := by intro same;subst i;simp [stepScratch,previousScratch,matchScratch] at member
      have d : i≠40 := by intro same;subst i;simp [stepScratch,previousScratch,matchScratch] at member
      simpa [next,stepResult,w.injective.eq_iff,a,b,c,d] using consumedEmpty i member
    obtain ⟨tailTime,tailBound,tailFinish,tailRun,tailHalt,tailStore⟩ := ih (before++[row]) next
      nextSource nextTable nextCounter nextVisited nextStatus nextBound nextEmpty
    have firstRun := repeat_iteration (w 23) (rowStep extra w) store true (List.replicate rest.length true)
      (by simpa only [List.length_cons,List.replicate_succ] using counter) bodyTime bodyFinish bodyRun bodyHalt
    change Machine.run (step (dedupRows extra w).program) (bodyTime+2) ⟨0,store⟩=some ⟨0,bodyFinish.store⟩ at firstRun
    have bodyLimit : bodyTime ≤ 2000*bound^2 := by
      apply bodyBound.trans
      apply Nat.mul_le_mul_left
      apply Nat.pow_le_pow_left
      simpa [consumed,w.injective.eq_iff] using sizeBound
    refine ⟨bodyTime+2+tailTime,?_,tailFinish,?_,tailHalt,?_⟩
    · simp only [List.length_cons];nlinarith only [bodyLimit,tailBound]
    · rw [Machine.run_add,firstRun,Option.bind_some,bodyResult]
      exact tailRun
    · rw [tailStore]
      funext r
      by_cases e0 : r=w 0
      · subst r;simp [dedupResult,w.injective.eq_iff]
      · by_cases e23 : r=w 23
        · subst r;simp [dedupResult,w.injective.eq_iff]
        · by_cases e36 : r=w 36
          · subst r
            by_cases seen : row∈before
            · simp [dedupResult,next,stepResult,consumed,freshRows,seen,w.injective.eq_iff]
            · simp [dedupResult,next,stepResult,consumed,freshRows,seen,w.injective.eq_iff,
                Encoding.sequence,List.reverse_append,List.append_assoc]
          · by_cases e41 : r=w 41
            · subst r
              by_cases seen : row∈before
              · simp [dedupResult,next,stepResult,consumed,freshRows,seen,w.injective.eq_iff]
              · simp [dedupResult,next,stepResult,consumed,freshRows,seen,w.injective.eq_iff,
                  List.replicate_succ,unaryPrefix_push]
            · by_cases e40 : r=w 40
              · subst r
                simp [dedupResult,next,stepResult,consumed,w.injective.eq_iff,
                  List.replicate_succ,unaryPrefix_push]
              · simp [dedupResult,next,stepResult,consumed,e0,e23,e36,e41,e40]

end Counting.External.CoverNormalization
