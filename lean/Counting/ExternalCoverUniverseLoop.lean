import Counting.ExternalCoverElementAudit

namespace Counting.External.CoverVerification
open StackMachine StackMachine.Routine CoverMachine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

def allHits (rows : List (List Nat)) (mask : List Bool) (start : Nat) : Nat → Bool
  | 0 => true
  | count+1 => decide (hits rows mask start=1) && allHits rows mask (start+1) count

theorem allHits_iff (rows : List (List Nat)) (mask : List Bool) (start count : Nat) :
    allHits rows mask start count=true ↔ ∀ i<count,hits rows mask (start+i)=1 := by
  induction count generalizing start with
  | zero => simp [allHits]
  | succ count ih =>
    simp only [allHits,Bool.and_eq_true,decide_eq_true_eq,ih]
    constructor
    · rintro ⟨first,rest⟩ i bound
      cases i with
      | zero => simpa using first
      | succ i => simpa [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using rest i (by omega)
    · intro all
      refine ⟨by simpa using all 0 (by omega),?_⟩
      intro i bound
      simpa [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using all (i+1) (by omega)

theorem elementAuditCost_mono (stream count a b : Nat) (bounded : a ≤ b) :
    elementAuditCost stream count a ≤ elementAuditCost stream count b := by
  have sizes := Nat.size_le_size bounded
  simp only [elementAuditCost,prepareElementCost,Encoding.natural_length]
  gcongr

def universeLoop (extra : Nat) (w : RowWorkspace extra) : Routine (extra+46) := forEach (w 42) (elementAudit extra w)

def universeResult (w : RowWorkspace extra) (store : Fin (extra+48) → List Bool)
    (rows : List (List Nat)) (mask : List Bool) (start count : Nat) (accepted : Bool) (tail : List Bool) :=
  Function.update (Function.update (Function.update store (w 42) []) (w 37)
    (List.replicate count true++store (w 37))) (w 1) ((accepted && allHits rows mask start count)::tail)

theorem universeLoop_executes (extra : Nat) (w : RowWorkspace extra)
    (rows : List (List Nat)) (mask : List Bool) (count boundIndex : Nat)
    (store : Fin (extra+48) → List Bool) (start : Nat) (accepted : Bool) (tail : List Bool)
    (stream : store (w 34)=Encoding.sequence (Encoding.list Encoding.natural) rows)
    (witness : store (w 33)=mask) (rowsCount : store (w 25)=List.replicate rows.length true)
    (index : (store (w 37)).length=start) (sized : mask.length=rows.length)
    (counter : store (w 42)=List.replicate count true) (bounded : start+count ≤ boundIndex)
    (status : store (w 1)=accepted::tail) (empty : ∀ i∈elementScratch,store (w i)=[]) :
    ∃ time ≤ count*(elementAuditCost (store (w 34)).length rows.length boundIndex+2)+1,
      Executes (universeLoop extra w) store time (universeResult w store rows mask start count accepted tail) := by
  induction count generalizing store start accepted with
  | zero =>
    obtain ⟨ran,halted⟩ := repeat_empty (w 42) (elementAudit extra w) store counter
    have unchanged : universeResult w store rows mask start 0 accepted tail=store := by
      simp only [universeResult,List.replicate_zero,List.nil_append,allHits,Bool.and_true]
      have counterEmpty : store (w 42)=[] := counter
      rw [←counterEmpty,Function.update_eq_self,Function.update_eq_self,←status,Function.update_eq_self]
    exact ⟨1,by simp,⟨1,store⟩,ran,halted,unchanged.symm⟩
  | succ count ih =>
    let consumed := Function.update store (w 42) (List.replicate count true)
    have consumedEmpty (i : Fin 48) (member : i∈elementScratch) : consumed (w i)=[] := by
      have different : i≠42 := by intro same;subst i;simp [elementScratch,membershipScratch] at member
      simpa [consumed,w.injective.eq_iff,different] using empty i member
    obtain ⟨bodyTime,bodyBound,bodyFinish,bodyRun,bodyHalt,bodyStore⟩ := elementAudit_executes extra w rows mask start consumed accepted tail
      (by simp [consumed,w.injective.eq_iff,stream])
      (by simp [consumed,w.injective.eq_iff,witness])
      (by simp [consumed,w.injective.eq_iff,rowsCount])
      (by simp [consumed,w.injective.eq_iff,index]) sized
      (by simp [consumed,w.injective.eq_iff,status]) consumedEmpty
    let nextFlag := accepted && decide (hits rows mask start=1)
    let next := Function.update (Function.update consumed (w 1) (nextFlag::tail)) (w 37) (true::store (w 37))
    have bodyResult : bodyFinish.store=next := by simpa [next,nextFlag,consumed,w.injective.eq_iff] using bodyStore
    have nextStream : next (w 34)=Encoding.sequence (Encoding.list Encoding.natural) rows := by simp [next,consumed,w.injective.eq_iff,stream]
    have nextWitness : next (w 33)=mask := by simp [next,consumed,w.injective.eq_iff,witness]
    have nextRowsCount : next (w 25)=List.replicate rows.length true := by simp [next,consumed,w.injective.eq_iff,rowsCount]
    have nextIndex : (next (w 37)).length=start+1 := by simp [next,index]
    have nextCounter : next (w 42)=List.replicate count true := by simp [next,consumed,w.injective.eq_iff]
    have nextStatus : next (w 1)=nextFlag::tail := by simp [next,w.injective.eq_iff]
    have nextEmpty (i : Fin 48) (member : i∈elementScratch) : next (w i)=[] := by
      have a : i≠1 := by intro same;subst i;simp [elementScratch,membershipScratch] at member
      have b : i≠37 := by intro same;subst i;simp [elementScratch,membershipScratch] at member
      simpa [next,w.injective.eq_iff,a,b] using consumedEmpty i member
    obtain ⟨tailTime,tailBound,tailFinish,tailRun,tailHalt,tailStore⟩ := ih next (start+1) nextFlag nextStream nextWitness nextRowsCount nextIndex
      nextCounter (by omega) nextStatus nextEmpty
    have firstRun := repeat_iteration (w 42) (elementAudit extra w) store true (List.replicate count true)
      (by simpa only [List.replicate_succ] using counter) bodyTime bodyFinish bodyRun bodyHalt
    change Machine.run (step (universeLoop extra w).program) (bodyTime+2) ⟨0,store⟩=some ⟨0,bodyFinish.store⟩ at firstRun
    have bodyLimit : bodyTime ≤ elementAuditCost (store (w 34)).length rows.length boundIndex := by
      have same : consumed (w 34)=store (w 34) := by simp [consumed,w.injective.eq_iff]
      rw [same] at bodyBound
      exact bodyBound.trans (elementAuditCost_mono _ _ _ _ (by omega))
    have streamSame : next (w 34)=store (w 34) := by simp [next,consumed,w.injective.eq_iff]
    rw [streamSame] at tailBound
    refine ⟨bodyTime+2+tailTime,?_,tailFinish,?_,tailHalt,?_⟩
    · nlinarith only [bodyLimit,tailBound]
    · rw [Machine.run_add,firstRun,Option.bind_some,bodyResult]
      exact tailRun
    · rw [tailStore]
      funext r
      by_cases e42 : r=w 42
      · subst r;simp [universeResult,w.injective.eq_iff]
      · by_cases e37 : r=w 37
        · subst r;simp only [universeResult,Function.update_of_ne (show w 37≠w 1 by simp [w.injective.eq_iff]),
            Function.update_self,next,unary_insert]
        · by_cases e1 : r=w 1
          · subst r;simp [universeResult,nextFlag,allHits,Bool.and_assoc]
          · simp [universeResult,next,consumed,e42,e37,e1]

end Counting.External.CoverVerification
