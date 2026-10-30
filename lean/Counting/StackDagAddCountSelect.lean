import Counting.StackDagAddCountActions
import Counting.StackBinaryComparePreserving
import Counting.StackComparePreserving
import Counting.StackReadBranch

namespace Counting.StackMachine.DagUpdate
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

def AddWorkspace.comparison (w : AddWorkspace extra) : Fin 6 ↪ Fin (extra+20) :=
  (⟨![1,6,11,8,9,10],by decide⟩ : Fin 6 ↪ Fin 20).trans w

def compareCurrent (extra : Nat) (w : AddWorkspace extra) : Routine (extra+18) :=
  sequence (Binary.preservingComparison (extra+14) w.comparison)
    (branchRoutine (w 11) (insertCurrent extra w) (emitCurrent extra w))

def processActive (extra : Nat) (w : AddWorkspace extra) : Routine (extra+18) :=
  sequence (Compare.preservingEquality (extra+14) w.comparison)
    (branchRoutine (w 11) (mergeAndEmit extra w) (compareCurrent extra w))

def processCurrent (extra : Nat) (w : AddWorkspace extra) : Routine (extra+18) :=
  branchRead (w 4) (processActive extra w) (emitCurrent extra w)

def actionScratch : List (Fin 20) := [8,9,10,11,12,13,14,15,16]

theorem bits_eq_iff (a b : Nat) : a.bits=b.bits ↔ a=b := by
  constructor
  · intro same
    have value:=congrArg Encoding.value same
    simpa only [Encoding.value_bits] using value
  · intro same;rw [same]

theorem compare_bits_natural (a b : Nat) : Binary.compareBits true a.bits b.bits=decide (a ≤ b) := by
  apply Bool.eq_iff_iff.mpr
  rw [Binary.compareBits_le,Encoding.value_bits,Encoding.value_bits,decide_eq_true_eq]

theorem compareCurrent_executes (extra : Nat) (w : AddWorkspace extra) (store : Store (extra+18))
    (index count i c : Nat) (tail : List Bool)
    (query : store (w 1)=index.bits) (increment : store (w 2)=count.bits)
    (currentIndex : store (w 6)=i.bits) (currentCount : store (w 7)=c.bits)
    (flag : store (w 4)=true::tail) (different : index≠i)
    (empty : ∀ j∈actionScratch,store (w j)=[]) :
    ∃ time ≤ 50*(index.bits.length+count.bits.length+i.bits.length+c.bits.length)+100,
      Executes (compareCurrent extra w) store time
        (emittedResult w store (if index < i then [(index,count),(i,c)] else [(i,c)])
          (decide (¬index < i)) tail) := by
  have comparing:=Binary.preservingComparison_executes (extra+14) w.comparison store
    (by simpa [AddWorkspace.comparison] using empty 8 (by simp [actionScratch]))
    (by simpa [AddWorkspace.comparison] using empty 9 (by simp [actionScratch]))
    (by simpa [AddWorkspace.comparison] using empty 10 (by simp [actionScratch]))
  have queryAt : store (w.comparison 0)=index.bits := query
  have indexAt : store (w.comparison 1)=i.bits := currentIndex
  have outputAt : store (w.comparison 2)=[] := empty 11 (by simp [actionScratch])
  rw [queryAt,indexAt,outputAt,compare_bits_natural] at comparing
  have restore (bit : Bool) : Function.update (Function.update store (w 11) [bit]) (w 11) []=store := by
    rw [Function.update_idem,←empty 11 (by simp [actionScratch]),Function.update_eq_self]
  have comparisonBound:=Binary.preservingCompareCost_le index.bits i.bits
  by_cases smaller : index < i
  · have le : index ≤ i := by omega
    simp only [le,decide_true] at comparing
    have inserting:=insertCurrent_executes extra w store index count i c true tail
      query increment currentIndex currentCount flag (by
        intro j member
        apply empty
        simp only [List.mem_cons,List.not_mem_nil,or_false] at member
        simp only [actionScratch,List.mem_cons,List.not_mem_nil,or_false]
        tauto)
    have branch:=branch_executes_true (w 11) (insertCurrent extra w) (emitCurrent extra w)
      (Function.update store (w 11) [true]) _ [] _ (by simp) (by rw [restore];exact inserting)
    have combined:=comparing.sequence branch
    refine ⟨Binary.preservingCompareCost index.bits i.bits+1+
      (1+(14*(index.bits.length+count.bits.length)+9*(i.bits.length+c.bits.length)+49)),by omega,?_⟩
    simpa only [compareCurrent,smaller,if_true,not_true_eq_false,decide_false] using combined
  · have gt : ¬index ≤ i := by omega
    simp only [gt,decide_false] at comparing
    have emitting:=emitCurrent_result extra w store i c true tail currentIndex currentCount flag
      (empty 15 (by simp [actionScratch])) (empty 16 (by simp [actionScratch]))
    have branch:=branch_executes_false (w 11) (insertCurrent extra w) (emitCurrent extra w)
      (Function.update store (w 11) [false]) _ [] _ (by simp) (by rw [restore];exact emitting)
    have combined:=comparing.sequence branch
    refine ⟨Binary.preservingCompareCost index.bits i.bits+1+(1+(9*(i.bits.length+c.bits.length)+19)),by omega,?_⟩
    simpa only [compareCurrent,smaller,if_false,not_false_eq_true,decide_true] using combined

theorem processActive_executes (extra : Nat) (w : AddWorkspace extra) (store : Store (extra+18))
    (index count i c : Nat) (tail : List Bool)
    (query : store (w 1)=index.bits) (increment : store (w 2)=count.bits)
    (currentIndex : store (w 6)=i.bits) (currentCount : store (w 7)=c.bits)
    (flag : store (w 4)=true::tail) (empty : ∀ j∈actionScratch,store (w j)=[]) :
    ∃ time ≤ 100*(index.bits.length+count.bits.length+i.bits.length+c.bits.length)+150,
      Executes (processActive extra w) store time
        (emittedResult w store (Counting.DagUpdate.addCountStep index count true (i,c)).1
          (Counting.DagUpdate.addCountStep index count true (i,c)).2 tail) := by
  have comparing:=Compare.preservingEquality_executes (extra+14) w.comparison store
    (by simpa [AddWorkspace.comparison] using empty 8 (by simp [actionScratch]))
    (by simpa [AddWorkspace.comparison] using empty 9 (by simp [actionScratch]))
    (by simpa [AddWorkspace.comparison] using empty 10 (by simp [actionScratch]))
  have queryAt : store (w.comparison 0)=index.bits := query
  have indexAt : store (w.comparison 1)=i.bits := currentIndex
  have outputAt : store (w.comparison 2)=[] := empty 11 (by simp [actionScratch])
  rw [queryAt,indexAt,outputAt] at comparing
  simp only [bits_eq_iff] at comparing
  have restore (bit : Bool) : Function.update (Function.update store (w 11) [bit]) (w 11) []=store := by
    rw [Function.update_idem,←empty 11 (by simp [actionScratch]),Function.update_eq_self]
  have comparisonBound:=Compare.preservingCost_le index.bits i.bits
  by_cases equal : index=i
  · simp only [equal,decide_true] at comparing
    obtain ⟨time,bound,merging⟩:=mergeAndEmit_executes extra w store count i c true tail increment currentIndex currentCount flag (by
      intro j member
      apply empty
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      simp only [actionScratch,List.mem_cons,List.not_mem_nil,or_false]
      tauto)
    have branch:=branch_executes_true (w 11) (mergeAndEmit extra w) (compareCurrent extra w)
      (Function.update store (w 11) [true]) _ [] _ (by simp) (by rw [restore];exact merging)
    have combined:=comparing.sequence branch
    refine ⟨Compare.preservingCost i.bits i.bits+1+(1+time),?_,?_⟩
    · rw [equal] at comparisonBound ⊢
      omega
    · simpa [processActive,Counting.DagUpdate.addCountStep,equal] using combined
  · simp only [equal,decide_false] at comparing
    obtain ⟨time,bound,processing⟩:=compareCurrent_executes extra w store index count i c tail
      query increment currentIndex currentCount flag equal empty
    have branch:=branch_executes_false (w 11) (mergeAndEmit extra w) (compareCurrent extra w)
      (Function.update store (w 11) [false]) _ [] _ (by simp) (by rw [restore];exact processing)
    have combined:=comparing.sequence branch
    refine ⟨Compare.preservingCost index.bits i.bits+1+(1+time),by omega,?_⟩
    by_cases smaller : index < i
    all_goals simpa [processActive,Counting.DagUpdate.addCountStep,equal,smaller] using combined

theorem processCurrent_executes (extra : Nat) (w : AddWorkspace extra) (store : Store (extra+18))
    (index count i c : Nat) (pending : Bool) (tail : List Bool)
    (query : store (w 1)=index.bits) (increment : store (w 2)=count.bits)
    (currentIndex : store (w 6)=i.bits) (currentCount : store (w 7)=c.bits)
    (flag : store (w 4)=pending::tail) (empty : ∀ j∈actionScratch,store (w j)=[]) :
    ∃ time ≤ 100*(index.bits.length+count.bits.length+i.bits.length+c.bits.length)+153,
      Executes (processCurrent extra w) store time
        (emittedResult w store (Counting.DagUpdate.addCountStep index count pending (i,c)).1
          (Counting.DagUpdate.addCountStep index count pending (i,c)).2 tail) := by
  cases pending
  · have emitting:=emitCurrent_result extra w store i c false tail currentIndex currentCount flag
      (empty 15 (by simp [actionScratch])) (empty 16 (by simp [actionScratch]))
    have branch:=branchRead_executes (w 4) (processActive extra w) (emitCurrent extra w)
      false tail store _ _ flag emitting
    exact ⟨_,by omega,branch⟩
  · obtain ⟨time,bound,processing⟩:=processActive_executes extra w store index count i c tail
      query increment currentIndex currentCount flag empty
    have branch:=branchRead_executes (w 4) (processActive extra w) (emitCurrent extra w)
      true tail store _ _ flag processing
    exact ⟨_,by omega,branch⟩

end Counting.StackMachine.DagUpdate
