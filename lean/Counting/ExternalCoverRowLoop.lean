import Counting.ExternalCoverRow

namespace Counting.External.CoverMachine
open StackMachine StackMachine.Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

def shiftRow (q : Nat) : List Nat → List Nat
  | a::b::c::_ => [a,q+b,2*q+c]
  | _ => []
def shiftedRows (q : Nat) (rows : List (List Nat)) := rows.map (shiftRow q)

theorem generateRowList_executes (extra : Nat) (w : RowWorkspace extra)
    (store : Fin (extra+48) → List Bool) (row : List Nat) (accepted : Bool) (suffix tail : List Bool)
    (three : row.length=3) (source : store (w 0)=(Encoding.list Encoding.natural).encode row++suffix)
    (status : store (w 1)=accepted::tail) (fits : ∀ index∈row,index≤(store (w 17)).length)
    (empty : ∀ i∈rowScratch,store (w i)=[]) :
    ∃ time ≤ 4000*((store (w 0)).length+(store (w 17)).length+1)^3,
      Executes (generateRow extra w) store time
        (Function.update (Function.update store (w 0) suffix) (w 36)
          (((Encoding.list Encoding.natural).encode (shiftRow (store (w 17)).length row)).reverse++store (w 36))) := by
  cases row with
  | nil => simp at three
  | cons a rest =>
    cases rest with
    | nil => simp at three
    | cons b rest =>
      cases rest with
      | nil => simp at three
      | cons c rest =>
        have restEmpty : rest=[] := List.length_eq_zero_iff.mp (by simpa using three)
        subst rest
        exact generateRow_executes extra w store a b c accepted suffix tail source status
          (fits a (by simp)) (fits b (by simp)) (fits c (by simp)) empty

def generateRows (extra : Nat) (w : RowWorkspace extra) : Routine (extra+46) := forEach (w 23) (generateRow extra w)

def rowsResult (w : RowWorkspace extra) (store : Fin (extra+48) → List Bool) (q : Nat)
    (rows : List (List Nat)) (suffix : List Bool) :=
  Function.update (Function.update (Function.update store (w 0) suffix) (w 23) []) (w 36)
    ((Encoding.sequence (Encoding.list Encoding.natural) (shiftedRows q rows)).reverse++store (w 36))

theorem generateRows_executes (extra : Nat) (w : RowWorkspace extra) (rows : List (List Nat)) (q bound : Nat)
    (store : Fin (extra+48) → List Bool) (accepted : Bool) (suffix tail : List Bool)
    (source : store (w 0)=Encoding.sequence (Encoding.list Encoding.natural) rows++suffix)
    (counter : store (w 23)=List.replicate rows.length true)
    (status : store (w 1)=accepted::tail) (qValue : (store (w 17)).length=q)
    (sourceBound : (store (w 0)).length≤bound)
    (three : ∀ row∈rows,row.length=3) (fits : ∀ row∈rows,∀ index∈row,index≤q)
    (empty : ∀ i∈rowScratch,store (w i)=[]) :
    ∃ time ≤ rows.length*(4000*(bound+q+1)^3+2)+1,
      Executes (generateRows extra w) store time (rowsResult w store q rows suffix) := by
  induction rows generalizing store with
  | nil =>
    obtain ⟨ran,halted⟩ := repeat_empty (w 23) (generateRow extra w) store counter
    have unchanged : rowsResult w store q [] suffix=store := by
      simp only [rowsResult,shiftedRows,List.map_nil,Encoding.sequence,List.reverse_nil,List.nil_append]
      have sourceEq : store (w 0)=suffix := source
      have counterEmpty : store (w 23)=[] := counter
      rw [←sourceEq,Function.update_eq_self,←counterEmpty,Function.update_eq_self,Function.update_eq_self]
    exact ⟨1,by simp,⟨1,store⟩,ran,halted,unchanged.symm⟩
  | cons row rest ih =>
    let consumed := Function.update store (w 23) (List.replicate rest.length true)
    let remaining := Encoding.sequence (Encoding.list Encoding.natural) rest++suffix
    have consumedSource : consumed (w 0)=(Encoding.list Encoding.natural).encode row++remaining := by
      simpa [consumed,remaining,w.injective.eq_iff,Encoding.sequence,List.append_assoc] using source
    have consumedEmpty (i : Fin 48) (member : i∈rowScratch) : consumed (w i)=[] := by
      have different : i≠23 := by intro same;subst i;simp [rowScratch] at member
      simpa [consumed,w.injective.eq_iff,different] using empty i member
    obtain ⟨bodyTime,bodyBound,bodyFinish,bodyRun,bodyHalt,bodyStore⟩ := generateRowList_executes extra w consumed row accepted remaining tail
      (three row (by simp)) consumedSource (by simp [consumed,w.injective.eq_iff,status])
      (fun index mem=>by simpa [consumed,w.injective.eq_iff,qValue] using fits row (by simp) index mem) consumedEmpty
    let next := Function.update (Function.update consumed (w 0) remaining) (w 36)
      (((Encoding.list Encoding.natural).encode (shiftRow q row)).reverse++consumed (w 36))
    have bodyResult : bodyFinish.store=next := by simpa [next,consumed,w.injective.eq_iff,qValue] using bodyStore
    have nextSource : next (w 0)=Encoding.sequence (Encoding.list Encoding.natural) rest++suffix := by simp [next,w.injective.eq_iff,remaining]
    have nextCounter : next (w 23)=List.replicate rest.length true := by simp [next,consumed,w.injective.eq_iff]
    have nextStatus : next (w 1)=accepted::tail := by simp [next,consumed,w.injective.eq_iff,status]
    have nextQ : (next (w 17)).length=q := by simpa [next,consumed,w.injective.eq_iff] using qValue
    have nextBound : (next (w 0)).length≤bound := by
      rw [nextSource];rw [source] at sourceBound
      simp only [Encoding.sequence,List.length_append] at sourceBound ⊢;omega
    have nextEmpty (i : Fin 48) (member : i∈rowScratch) : next (w i)=[] := by
      have a : i≠0 := by intro same;subst i;simp [rowScratch] at member
      have b : i≠36 := by intro same;subst i;simp [rowScratch] at member
      simpa [next,w.injective.eq_iff,a,b] using consumedEmpty i member
    obtain ⟨tailTime,tailBound,tailFinish,tailRun,tailHalt,tailStore⟩ := ih next nextSource nextCounter nextStatus nextQ nextBound
      (fun row member=>three row (by simp [member])) (fun row member=>fits row (by simp [member])) nextEmpty
    have firstRun := repeat_iteration (w 23) (generateRow extra w) store true (List.replicate rest.length true)
      (by simpa only [List.length_cons,List.replicate_succ] using counter) bodyTime bodyFinish bodyRun bodyHalt
    change Machine.run (step (generateRows extra w).program) (bodyTime+2) ⟨0,store⟩=some ⟨0,bodyFinish.store⟩ at firstRun
    have bodyLimit : bodyTime≤4000*(bound+q+1)^3 := by
      apply bodyBound.trans;apply Nat.mul_le_mul_left;apply Nat.pow_le_pow_left
      simpa [consumed,w.injective.eq_iff,qValue] using Nat.add_le_add_right (Nat.add_le_add_right sourceBound q) 1
    refine ⟨bodyTime+2+tailTime,?_,tailFinish,?_,tailHalt,?_⟩
    · simp only [List.length_cons];nlinarith only [bodyLimit,tailBound]
    · rw [Machine.run_add,firstRun,Option.bind_some,bodyResult]
      exact tailRun
    · rw [tailStore]
      funext r
      by_cases e0 : r=w 0
      · subst r;simp [rowsResult,w.injective.eq_iff]
      · by_cases e23 : r=w 23
        · subst r;simp [rowsResult,w.injective.eq_iff]
        · by_cases e36 : r=w 36
          · subst r;simp [rowsResult,shiftedRows,next,consumed,w.injective.eq_iff,Encoding.sequence,List.reverse_append,List.append_assoc]
          · simp [rowsResult,next,consumed,e0,e23,e36]

end Counting.External.CoverMachine
