import Counting.StackDagSortCompleteStep

namespace Counting.StackMachine.DagUpdate.Sort
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

def insertFold (records sorted : List Record) : List Record :=
  records.foldl (fun previous query=>List.orderedInsert (fun a b=>recordLE a b=true) query previous) sorted

theorem insertFold_length (records sorted : List Record) :
    (insertFold records sorted).length=sorted.length+records.length := by
  induction records generalizing sorted with
  | nil=>simp [insertFold]
  | cons head tail ih=>
    change (insertFold tail (List.orderedInsert (fun a b=>recordLE a b=true) head sorted)).length=_
    rw [ih,List.orderedInsert_length]
    simp only [List.length_cons]
    omega

theorem insertFold_encoded_length (records sorted : List Record) :
    (Encoding.sequence recordCodec (insertFold records sorted)).length=
      (Encoding.sequence recordCodec records).length+(Encoding.sequence recordCodec sorted).length := by
  induction records generalizing sorted with
  | nil=>simp [insertFold,Encoding.sequence]
  | cons head tail ih=>
    change (Encoding.sequence recordCodec
      (insertFold tail (List.orderedInsert (fun a b=>recordLE a b=true) head sorted))).length=_
    rw [ih,orderedInsert_encoded_length]
    simp only [Encoding.sequence,List.length_append]
    omega

def sortLoop : Routine 94 := forEach 93 sortStep

def sortLoopResult (store : Store 94) (records sorted : List Record) (suffix : List Bool) : Store 94 :=
  Function.update (Function.update (Function.update (Function.update store 93 []) 92 suffix)
    80 (Encoding.sequence recordCodec (insertFold records sorted)))
    94 (List.replicate (sorted.length+records.length) true)

/-- Every outer iteration performs a physically charged stable insertion.
The combined unread and sorted payload length is invariant. -/
theorem sortLoop_executes (store : Store 94) (records sorted : List Record) (suffix : List Bool)
    (source : store 92=Encoding.sequence recordCodec records++suffix)
    (current : store 80=Encoding.sequence recordCodec sorted)
    (status : store 81=[true]) (counter : store 93=List.replicate records.length true)
    (inserted : store 94=List.replicate sorted.length true) (empty : SortEmpty store)
    (budget : Nat) (size : (store 92).length+(store 80).length≤budget) :
    ∃time≤records.length*(25000*(budget+1)^4+2)+1,
      Executes sortLoop store time (sortLoopResult store records sorted suffix) := by
  induction records generalizing store sorted with
  | nil=>
    have sourceAt:store 92=suffix:=by simpa [Encoding.sequence] using source
    have counterAt:store 93=[]:=by simpa using counter
    obtain ⟨ran,halted⟩:=repeat_empty (93:Fin 96) sortStep store counterAt
    have final:store=sortLoopResult store [] sorted suffix:=by
      funext r
      by_cases r80:r=80 <;> by_cases r92:r=92 <;> by_cases r93:r=93 <;> by_cases r94:r=94 <;>
        simp [sortLoopResult,insertFold,r80,r92,r93,r94,sourceAt,counterAt,current,inserted]
    exact ⟨1,by simp,⟨1,store⟩,ran,halted,final⟩
  | cons query records ih=>
    let consumed:=Function.update store 93 (List.replicate records.length true)
    let remaining:=Encoding.sequence recordCodec records++suffix
    let next:=List.orderedInsert (fun a b=>recordLE a b=true) query sorted
    have consumedEmpty:SortEmpty consumed:=by
      intro r allowed
      have ne:r≠93:=by intro same;subst r;norm_num [Fin.ext_iff] at allowed
      simpa [consumed,ne] using empty r allowed
    obtain ⟨bodyTime,bodyBound,bodyExec⟩:=sortStep_executes consumed query sorted remaining
      (by simpa [consumed,remaining,Encoding.sequence,List.append_assoc] using source)
      (by simp [consumed,current]) (by simp [consumed,status])
      (by simp [consumed,inserted]) consumedEmpty
    let middle:=sortStepResult consumed query sorted remaining
    have middleSource:middle 92=Encoding.sequence recordCodec records++suffix:=by
      simp [middle,sortStepResult,remaining]
    have middleCurrent:middle 80=Encoding.sequence recordCodec next:=by
      simp [middle,sortStepResult,next]
    have middleStatus:middle 81=[true]:=by simp [middle,sortStepResult,consumed,status]
    have middleCounter:middle 93=List.replicate records.length true:=by simp [middle,sortStepResult,consumed]
    have middleInserted:middle 94=List.replicate next.length true:=by
      simp [middle,sortStepResult,consumed,inserted,next,List.orderedInsert_length,List.replicate_succ]
    have middleEmpty:SortEmpty middle:=by
      intro r allowed
      have n80:r≠80:=by intro same;subst r;norm_num [Fin.ext_iff] at allowed
      have n92:r≠92:=by intro same;subst r;norm_num [Fin.ext_iff] at allowed
      have n94:r≠94:=by intro same;subst r;norm_num [Fin.ext_iff] at allowed
      simpa [middle,sortStepResult,n80,n92,n94] using consumedEmpty r allowed
    have middleSize:(middle 92).length+(middle 80).length≤budget:=by
      rw [middleSource,middleCurrent]
      rw [source,current] at size
      simp only [Encoding.sequence,List.length_append] at size
      simp only [next,orderedInsert_encoded_length,List.length_append]
      omega
    obtain ⟨tailTime,tailBound,tailExec⟩:=ih middle next middleSource middleCurrent middleStatus
      middleCounter middleInserted middleEmpty middleSize
    obtain ⟨bodyFinal,bodyRun,bodyHalt,bodyStore⟩:=bodyExec
    obtain ⟨finish,tailRun,tailHalt,tailStore⟩:=tailExec
    have first:=repeat_iteration (93:Fin 96) sortStep store true (List.replicate records.length true)
      (by simpa only [List.length_cons,List.replicate_succ] using counter) bodyTime bodyFinal bodyRun bodyHalt
    change Machine.run (step sortLoop.program) (bodyTime+2) ⟨0,store⟩=some ⟨0,bodyFinal.store⟩ at first
    have final:sortLoopResult middle records next suffix=
        sortLoopResult store (query::records) sorted suffix:=by
      funext r
      by_cases r80:r=80 <;> by_cases r92:r=92 <;> by_cases r93:r=93 <;> by_cases r94:r=94 <;>
        simp [sortLoopResult,middle,sortStepResult,consumed,insertFold,next,List.orderedInsert_length,
          Nat.add_comm,Nat.add_left_comm,r80,r92,r93,r94]
    refine ⟨bodyTime+2+tailTime,?_,finish,?_,tailHalt,tailStore.trans final⟩
    · have consumed92:consumed 92=store 92:=by simp [consumed]
      have consumed80:consumed 80=store 80:=by simp [consumed]
      rw [consumed92,consumed80] at bodyBound
      have bound:=bodyBound.trans (Nat.mul_le_mul_left 25000
        (Nat.pow_le_pow_left (Nat.add_le_add_right size 1) 4))
      simp only [List.length_cons]
      nlinarith
    · rw [Machine.run_add,first,Option.bind_some,bodyStore]
      exact tailRun

end Counting.StackMachine.DagUpdate.Sort
