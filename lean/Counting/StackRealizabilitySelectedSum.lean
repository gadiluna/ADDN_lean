import Counting.StackRealizabilityPreservingSum
import Counting.StackComparePreserving
import Counting.StackEncodingBranch
import Counting.StackEncodingRoutineInterfaces
import Counting.StackEncodingGuards

namespace Counting.StackMachine.RealizabilityCheck
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

def selectedFirstRoles : Fin 6 ↪ Fin 10:=⟨![0,1,6,7,8,9],by decide⟩
def selectedSecondRoles : Fin 6 ↪ Fin 10:=⟨![2,3,6,7,8,9],by decide⟩
def selectedSumRoles : Fin 5 ↪ Fin 10:=⟨![5,4,7,8,9],by decide⟩

/-- Two preserved binary equality tests select a contribution. This is
used for the next-level and parent constraints of `childCount`. -/
def selectedSum : Routine 8:=sequence (Compare.preservingEquality 4 selectedFirstRoles)
  (sequence (Compare.preservingEquality 4 selectedSecondRoles)
    (sequence (ofProgram (combineFlagsProgram 8 6))
      (branchRoutine 6 (preservingSum 5 selectedSumRoles) (skip 8))))

def selectedSumCondition (store : Store 8) : Bool:=
  decide (store 0=store 1) && decide (store 2=store 3)

theorem selectedSum_executes (store : Store 8)
    (empty : ∀ r : Fin 10,6 ≤ r.val → store r=[]) :
    ∃ time ≤ 60*((store 0).length+(store 1).length+(store 2).length+(store 3).length+
        (store 4).length+(store 5).length+1),
      Executes selectedSum store time
        (if selectedSumCondition store then Function.update store 5
          (Encoding.value (store 5)+Encoding.value (store 4)).bits else store):=by
  let first:=decide (store 0=store 1)
  let second:=decide (store 2=store 3)
  have firstRun:=Compare.preservingEquality_executes 4 selectedFirstRoles store
    (empty 7 (by decide)) (empty 8 (by decide)) (empty 9 (by decide))
  change Executes (Compare.preservingEquality 4 selectedFirstRoles) store
    (Compare.preservingCost (store 0) (store 1)) (Function.update store 6 (first::store 6)) at firstRun
  rw [empty 6 (by decide)] at firstRun
  let firstStore:=Function.update store 6 [first]
  have secondRun:=Compare.preservingEquality_executes 4 selectedSecondRoles firstStore
    (by simp [selectedSecondRoles,firstStore,empty])
    (by simp [selectedSecondRoles,firstStore,empty])
    (by simp [selectedSecondRoles,firstStore,empty])
  change Executes (Compare.preservingEquality 4 selectedSecondRoles) firstStore
    (Compare.preservingCost (firstStore 2) (firstStore 3))
      (Function.update firstStore 6 (decide (firstStore 2=firstStore 3)::firstStore 6)) at secondRun
  have secondResult : Function.update firstStore 6 (decide (firstStore 2=firstStore 3)::firstStore 6)=
      Function.update store 6 [second,first]:=by simp [firstStore,second]
  rw [secondResult] at secondRun
  have secondLeft : firstStore 2=store 2:=by simp [firstStore]
  have secondRight : firstStore 3=store 3:=by simp [firstStore]
  rw [secondLeft,secondRight] at secondRun
  let bothStore:=Function.update store 6 [second,first]
  have combining:=combineFlags_executes 8 6 bothStore first second [] (by simp [bothStore])
  have combinedStore : Function.update bothStore 6 [first&&second]=Function.update store 6 [first&&second]:=by
    simp [bothStore]
  rw [combinedStore] at combining
  let checked:=Function.update store 6 [first&&second]
  have restored : Function.update checked 6 []=store:=by
    simp only [checked,Function.update_idem,←empty 6 (by decide),Function.update_eq_self]
  have firstCost:=Compare.preservingCost_le (store 0) (store 1)
  have secondCost:=Compare.preservingCost_le (store 2) (store 3)
  by_cases selected : (first&&second)=true
  · obtain ⟨sumTime,sumBound,summing⟩:=preservingSum_executes 5 selectedSumRoles store
      (empty 7 (by decide)) (empty 8 (by decide)) (empty 9 (by decide))
    change sumTime ≤ 30*((store 5).length+(store 4).length+1) at sumBound
    change Executes (preservingSum 5 selectedSumRoles) store sumTime
      (Function.update store 5 (Encoding.value (store 5)+Encoding.value (store 4)).bits) at summing
    have branched:=branch_executes_true (6:Fin 10) (preservingSum 5 selectedSumRoles) (skip 8) checked
      _ [] sumTime (by simp [checked,selected]) (by rw [restored];exact summing)
    have condition : selectedSumCondition store=true:=selected
    rw [condition]
    exact ⟨_,by omega,firstRun.sequence (secondRun.sequence (combining.sequence branched))⟩
  · have condition : (first&&second)=false:=Bool.eq_false_iff.mpr selected
    have branched:=branch_executes_false (6:Fin 10) (preservingSum 5 selectedSumRoles) (skip 8) checked
      store [] 0 (by simp [checked,condition]) (by rw [restored];exact Routine.skip_executes store)
    have failed : selectedSumCondition store=false:=condition
    rw [failed]
    exact ⟨_,by omega,firstRun.sequence (secondRun.sequence (combining.sequence branched))⟩

theorem selectedSumCondition_naturals (store : Store 8) (level target parent old : Nat)
    (a : store 0=level.bits) (b : store 1=target.bits) (c : store 2=parent.bits) (d : store 3=old.bits) :
    selectedSumCondition store=decide (level=target ∧ parent=old):=by
  apply Bool.eq_iff_iff.mpr
  simp only [selectedSumCondition,a,b,c,d,Encoding.bits_injective.eq_iff,Bool.and_eq_true,decide_eq_true_eq]

end Counting.StackMachine.RealizabilityCheck
