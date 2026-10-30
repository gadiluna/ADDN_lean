import Counting.ExternalCoverNormalizeAtom

namespace Counting.External.CoverNormalization
open StackMachine StackMachine.Routine SATVerification CoverMachine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def matchPrefix (extra : Nat) (w : RowWorkspace extra) : Routine (extra+46) := forEach (w 24) (matchAtom extra w)

def matchingRow (query : List Bool) (indices : List MatchingVerification.RawClause) : Bool :=
  indices.any (fun index=>decide (MatchingVerification.clauseCodec.encode index=query))

def matchPrefixResult (w : RowWorkspace extra) (store : Fin (extra+48) → List Bool)
    (indices : List MatchingVerification.RawClause) (suffix : List Bool) (value : Bool) (accumulatorTail : List Bool) :=
  Function.update (Function.update (Function.update store (w 0) suffix) (w 24) []) (w 22)
    ((value || matchingRow (store (w 38)) indices)::accumulatorTail)

theorem matchPrefix_executes (extra : Nat) (w : RowWorkspace extra) (indices : List MatchingVerification.RawClause) (bound : Nat)
    (store : Fin (extra+48) → List Bool) (accepted value : Bool) (suffix tail accumulatorTail : List Bool)
    (source : store (w 0)=Encoding.sequence MatchingVerification.clauseCodec indices++suffix)
    (counter : store (w 24)=List.replicate indices.length true)
    (status : store (w 1)=accepted::tail) (accumulated : store (w 22)=value::accumulatorTail)
    (sourceBound : (store (w 0)).length≤bound)
    (empty : ∀ i∈matchScratch,store (w i)=[]) :
    ∃ time ≤ indices.length*(210*(bound+(store (w 38)).length+1)+2)+1,
      Executes (matchPrefix extra w) store time (matchPrefixResult w store indices suffix value accumulatorTail) := by
  induction indices generalizing store value with
  | nil =>
    obtain ⟨ran,halted⟩ := repeat_empty (w 24) (matchAtom extra w) store counter
    have unchanged : matchPrefixResult w store [] suffix value accumulatorTail=store := by
      simp only [matchPrefixResult,matchingRow,List.any_nil,Bool.or_false]
      have sourceEq : store (w 0)=suffix := source
      have counterEmpty : store (w 24)=[] := counter
      rw [←sourceEq,Function.update_eq_self,←counterEmpty,Function.update_eq_self,←accumulated,Function.update_eq_self]
    exact ⟨1,by simp,⟨1,store⟩,ran,halted,unchanged.symm⟩
  | cons index rest ih =>
    let consumed := Function.update store (w 24) (List.replicate rest.length true)
    let remaining := Encoding.sequence MatchingVerification.clauseCodec rest++suffix
    have consumedSource : consumed (w 0)=MatchingVerification.clauseCodec.encode index++remaining := by
      simpa [consumed,remaining,w.injective.eq_iff,Encoding.sequence,List.append_assoc] using source
    have consumedEmpty (i : Fin 48) (member : i∈matchScratch) : consumed (w i)=[] := by
      have different : i≠24 := by intro same;subst i;simp [matchScratch] at member
      simpa [consumed,w.injective.eq_iff,different] using empty i member
    obtain ⟨bodyTime,bodyBound,bodyFinish,bodyRun,bodyHalt,bodyStore⟩ := matchAtom_executes extra w consumed index accepted value remaining tail accumulatorTail
      consumedSource (by simp [consumed,w.injective.eq_iff,status])
      (by simp [consumed,w.injective.eq_iff,accumulated]) consumedEmpty
    let bit := decide (MatchingVerification.clauseCodec.encode index=store (w 38))
    let next := Function.update (Function.update consumed (w 0) remaining) (w 22) ((value || bit)::accumulatorTail)
    have bodyResult : bodyFinish.store=next := by simpa [next,bit,consumed,w.injective.eq_iff] using bodyStore
    have nextSource : next (w 0)=Encoding.sequence MatchingVerification.clauseCodec rest++suffix := by simp [next,w.injective.eq_iff,remaining]
    have nextCounter : next (w 24)=List.replicate rest.length true := by simp [next,consumed,w.injective.eq_iff]
    have nextStatus : next (w 1)=accepted::tail := by simp [next,consumed,w.injective.eq_iff,status]
    have nextAccumulated : next (w 22)=(value || bit)::accumulatorTail := by simp [next]
    have nextBound : (next (w 0)).length≤bound := by
      rw [nextSource];rw [source] at sourceBound
      simp only [Encoding.sequence,List.length_append] at sourceBound ⊢;omega
    have nextEmpty (i : Fin 48) (member : i∈matchScratch) : next (w i)=[] := by
      have a : i≠0 := by intro same;subst i;simp [matchScratch] at member
      have b : i≠22 := by intro same;subst i;simp [matchScratch] at member
      simpa [next,w.injective.eq_iff,a,b] using consumedEmpty i member
    obtain ⟨tailTime,tailBound,tailFinish,tailRun,tailHalt,tailStore⟩ := ih next (value || bit) nextSource nextCounter nextStatus nextAccumulated nextBound nextEmpty
    have firstRun := repeat_iteration (w 24) (matchAtom extra w) store true (List.replicate rest.length true)
      (by simpa only [List.length_cons,List.replicate_succ] using counter) bodyTime bodyFinish bodyRun bodyHalt
    change Machine.run (step (matchPrefix extra w).program) (bodyTime+2) ⟨0,store⟩=some ⟨0,bodyFinish.store⟩ at firstRun
    have bodyLimit : bodyTime≤210*(bound+(store (w 38)).length+1) := by
      change bodyTime≤210*((consumed (w 0)).length+(consumed (w 38)).length+1) at bodyBound
      simp only [consumed,Function.update_of_ne (show w 0≠w 24 by simp [w.injective.eq_iff]),
        Function.update_of_ne (show w 38≠w 24 by simp [w.injective.eq_iff])] at bodyBound
      omega
    have query : next (w 38)=store (w 38) := by simp [next,consumed,w.injective.eq_iff]
    rw [query] at tailBound
    refine ⟨bodyTime+2+tailTime,?_,tailFinish,?_,tailHalt,?_⟩
    · simp only [List.length_cons];nlinarith only [bodyLimit,tailBound]
    · rw [Machine.run_add,firstRun,Option.bind_some,bodyResult]
      exact tailRun
    · rw [tailStore]
      funext r
      by_cases e0 : r=w 0
      · subst r;simp [matchPrefixResult,w.injective.eq_iff]
      · by_cases e24 : r=w 24
        · subst r;simp [matchPrefixResult,w.injective.eq_iff]
        · by_cases e22 : r=w 22
          · subst r;simp [matchPrefixResult,matchingRow,next,consumed,w.injective.eq_iff,List.any_cons,Bool.or_assoc,bit]
          · simp [matchPrefixResult,next,consumed,e0,e24,e22]

end Counting.External.CoverNormalization
