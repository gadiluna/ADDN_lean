import Counting.ExternalCoverMaskedRow
import Counting.ExternalCoverMaskSemantics

namespace Counting.External.CoverVerification
open StackMachine StackMachine.Routine CoverMachine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

def maskedRows (extra : Nat) (w : RowWorkspace extra) : Routine (extra+46) := forEach (w 23) (maskedRow extra w)

theorem unary_insert (count : Nat) (tail : List Bool) :
    List.replicate count true++true::tail=List.replicate (count+1) true++tail := by
  rw [List.replicate_succ',List.append_assoc]
  rfl

def maskedRowsResult (w : RowWorkspace extra) (store : Fin (extra+48) → List Bool)
    (rows : List (List Nat)) (mask : List Bool) (element : Nat) (suffix maskTail : List Bool) :=
  Function.update (Function.update (Function.update (Function.update store (w 0) suffix) (w 23) [])
    (w 32) maskTail) (w 35) (List.replicate (hits rows mask element) true++store (w 35))

theorem maskedRows_executes (extra : Nat) (w : RowWorkspace extra) (rows : List (List Nat)) (element bound : Nat)
    (mask : List Bool) (store : Fin (extra+48) → List Bool) (accepted : Bool) (suffix tail maskTail : List Bool)
    (source : store (w 0)=Encoding.sequence (Encoding.list Encoding.natural) rows++suffix)
    (counter : store (w 23)=List.replicate rows.length true)
    (status : store (w 1)=accepted::tail) (query : store (w 38)=Encoding.natural.encode element)
    (witness : store (w 32)=mask++maskTail) (sized : mask.length=rows.length)
    (sourceBound : (store (w 0)).length ≤ bound)
    (empty : ∀ i∈membershipScratch,store (w i)=[]) :
    ∃ time ≤ rows.length*(2100*(bound+(store (w 38)).length+1)^3+2)+1,
      Executes (maskedRows extra w) store time (maskedRowsResult w store rows mask element suffix maskTail) := by
  induction rows generalizing mask store with
  | nil =>
    have maskEmpty : mask=[] := List.length_eq_zero_iff.mp sized
    subst mask
    obtain ⟨ran,halted⟩ := repeat_empty (w 23) (maskedRow extra w) store counter
    have unchanged : maskedRowsResult w store [] [] element suffix maskTail=store := by
      simp only [maskedRowsResult,hits,List.replicate_zero,List.nil_append]
      have sourceEq : store (w 0)=suffix := source
      have counterEmpty : store (w 23)=[] := counter
      have witnessEq : store (w 32)=maskTail := witness
      rw [←sourceEq,Function.update_eq_self,←counterEmpty,Function.update_eq_self,
        ←witnessEq,Function.update_eq_self,Function.update_eq_self]
    exact ⟨1,by simp,⟨1,store⟩,ran,halted,unchanged.symm⟩
  | cons row rest ih =>
    cases mask with
    | nil => simp at sized
    | cons bit bits =>
    let consumed := Function.update store (w 23) (List.replicate rest.length true)
    let remaining := Encoding.sequence (Encoding.list Encoding.natural) rest++suffix
    have consumedSource : consumed (w 0)=(Encoding.list Encoding.natural).encode row++remaining := by
      simpa [consumed,remaining,w.injective.eq_iff,Encoding.sequence,List.append_assoc] using source
    have consumedEmpty (i : Fin 48) (member : i∈membershipScratch) : consumed (w i)=[] := by
      have different : i≠23 := by intro same;subst i;simp [membershipScratch] at member
      simpa [consumed,w.injective.eq_iff,different] using empty i member
    obtain ⟨bodyTime,bodyBound,bodyFinish,bodyRun,bodyHalt,bodyStore⟩ := maskedRow_executes extra w row element consumed accepted bit remaining tail (bits++maskTail)
      consumedSource (by simp [consumed,w.injective.eq_iff,status])
      (by simp [consumed,w.injective.eq_iff,query])
      (by simpa [consumed,w.injective.eq_iff] using witness) consumedEmpty
    let next := maskedRowResult w consumed row element bit remaining (bits++maskTail)
    have bodyResult : bodyFinish.store=next := bodyStore
    have nextSource : next (w 0)=Encoding.sequence (Encoding.list Encoding.natural) rest++suffix := by simp [next,maskedRowResult,w.injective.eq_iff,remaining]
    have nextCounter : next (w 23)=List.replicate rest.length true := by simp [next,maskedRowResult,consumed,w.injective.eq_iff]
    have nextStatus : next (w 1)=accepted::tail := by simp [next,maskedRowResult,consumed,w.injective.eq_iff,status]
    have nextQuery : next (w 38)=Encoding.natural.encode element := by simp [next,maskedRowResult,consumed,w.injective.eq_iff,query]
    have nextWitness : next (w 32)=bits++maskTail := by simp [next,maskedRowResult,w.injective.eq_iff]
    have nextBound : (next (w 0)).length ≤ bound := by
      rw [nextSource];rw [source] at sourceBound
      simp only [Encoding.sequence,List.length_append] at sourceBound ⊢;omega
    have nextEmpty (i : Fin 48) (member : i∈membershipScratch) : next (w i)=[] := by
      have a : i≠0 := by intro same;subst i;simp [membershipScratch] at member
      have b : i≠32 := by intro same;subst i;simp [membershipScratch] at member
      have c : i≠35 := by intro same;subst i;simp [membershipScratch] at member
      simpa [next,maskedRowResult,w.injective.eq_iff,a,b,c] using consumedEmpty i member
    obtain ⟨tailTime,tailBound,tailFinish,tailRun,tailHalt,tailStore⟩ := ih bits next nextSource nextCounter nextStatus nextQuery nextWitness
      (by simpa using sized) nextBound nextEmpty
    have firstRun := repeat_iteration (w 23) (maskedRow extra w) store true (List.replicate rest.length true)
      (by simpa only [List.length_cons,List.replicate_succ] using counter) bodyTime bodyFinish bodyRun bodyHalt
    change Machine.run (step (maskedRows extra w).program) (bodyTime+2) ⟨0,store⟩=some ⟨0,bodyFinish.store⟩ at firstRun
    have bodyLimit : bodyTime ≤ 2100*(bound+(store (w 38)).length+1)^3 := by
      apply bodyBound.trans
      apply Nat.mul_le_mul_left
      apply Nat.pow_le_pow_left
      simpa [consumed,w.injective.eq_iff] using Nat.add_le_add_right (Nat.add_le_add_right sourceBound (store (w 38)).length) 1
    have querySame : next (w 38)=store (w 38) := by simp [next,maskedRowResult,consumed,w.injective.eq_iff]
    rw [querySame] at tailBound
    refine ⟨bodyTime+2+tailTime,?_,tailFinish,?_,tailHalt,?_⟩
    · simp only [List.length_cons];nlinarith only [bodyLimit,tailBound]
    · rw [Machine.run_add,firstRun,Option.bind_some,bodyResult]
      exact tailRun
    · rw [tailStore]
      funext r
      by_cases e0 : r=w 0
      · subst r;simp [maskedRowsResult,w.injective.eq_iff]
      · by_cases e23 : r=w 23
        · subst r;simp [maskedRowsResult,w.injective.eq_iff]
        · by_cases e32 : r=w 32
          · subst r;simp [maskedRowsResult,w.injective.eq_iff]
          · by_cases e35 : r=w 35
            · subst r
              simp only [maskedRowsResult,Function.update_self,next,maskedRowResult]
              simp only [consumed,Function.update_of_ne (show w 35≠w 23 by simp [w.injective.eq_iff]),hits]
              cases bit && row.contains element with
              | false => simp
              | true =>
                change List.replicate (hits rest bits element) true++true::store (w 35)=
                  List.replicate (1+hits rest bits element) true++store (w 35)
                simpa only [Nat.add_comm 1 (hits rest bits element)] using unary_insert (hits rest bits element) (store (w 35))
            · simp [maskedRowsResult,next,maskedRowResult,consumed,e0,e23,e32,e35]

end Counting.External.CoverVerification
