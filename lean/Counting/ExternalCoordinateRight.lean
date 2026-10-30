import Counting.ExternalCoordinateLeft
import Counting.StackSubtractLength

namespace Counting.External.CookLevin.StackGenerator
open StackMachine StackMachine.Routine

abbrev RightWorkspace (extra : Nat) := Fin 7 ↪ Fin (extra+7)

/-- Roles: center, width, place, result, remainder, counter, copy work. -/
def rightPrepare (extra : Nat) (w : RightWorkspace extra) : Routine (extra+5) :=
  sequence (ofProgram (ListPrograms.copyProgram (extra+4) (w 0) (w 3) (w 6)))
    (sequence (pushBit (w 3) true)
      (sequence (ofProgram (ListPrograms.copyProgram (extra+4) (w 1) (w 4) (w 6)))
        (sequence (subtractLength (extra+3) (w 2) (w 4) (w 5) (w 6)) (discard (w 4) 1))))

def rightPrepared (w : RightWorkspace extra) (store : Fin (extra+7) → List Bool) (center width place : Nat) :=
  Function.update (Function.update store (w 3) (List.replicate (center+1) true))
    (w 4) (List.replicate (width-place-1) true)

def rightPrepareCost (center width place : Nat) := 5*center+5*width+7*place+15

theorem rightPrepare_executes (extra : Nat) (w : RightWorkspace extra) (center width place : Nat)
    (store : Fin (extra+7) → List Bool)
    (centerValue : store (w 0)=List.replicate center true)
    (widthValue : store (w 1)=List.replicate width true)
    (placeValue : store (w 2)=List.replicate place true)
    (outputEmpty : store (w 3)=[]) (remainderEmpty : store (w 4)=[])
    (counterEmpty : store (w 5)=[]) (workEmpty : store (w 6)=[]) :
    Executes (rightPrepare extra w) store (rightPrepareCost center width place)
      (rightPrepared w store center width place) := by
  have distinct {a b : Fin 7} (different : a ≠ b) : w a ≠ w b := fun same => different (w.injective same)
  let copied := Function.update store (w 3) (List.replicate center true)
  have copy : Executes (ofProgram (ListPrograms.copyProgram (extra+4) (w 0) (w 3) (w 6))) store
      (5*center+2) copied := by
    simpa +instances only [ListPrograms.copyProgram,centerValue,outputEmpty,List.length_replicate,List.append_nil,copied] using
      copy_executes (extra+4) (w 0) (w 3) (w 6)
        (distinct (by decide)) (distinct (by decide)) (distinct (by decide)) store workEmpty
  let incremented := Function.update store (w 3) (List.replicate (center+1) true)
  have push : Executes (pushBit (w 3) true) copied 1 incremented := by
    simpa only [copied,incremented,Function.update_self,Function.update_idem,List.replicate_succ] using
      pushBit_executes (w 3) true copied
  let added := Function.update incremented (w 4) (List.replicate width true)
  have addWidth : Executes (ofProgram (ListPrograms.copyProgram (extra+4) (w 1) (w 4) (w 6))) incremented
      (5*width+2) added := by
    have run := copy_executes (extra+4) (w 1) (w 4) (w 6)
      (distinct (by decide)) (distinct (by decide)) (distinct (by decide)) incremented
      (by simp [incremented,w.injective.eq_iff,workEmpty])
    have source : incremented (w 1)=List.replicate width true := by simp [incremented,w.injective.eq_iff,widthValue]
    have target : incremented (w 4)=[] := by simp [incremented,w.injective.eq_iff,remainderEmpty]
    simpa +instances only [ListPrograms.copyProgram,source,target,List.length_replicate,List.append_nil,added] using run
  let subtracted := Function.update incremented (w 4) (List.replicate (width-place) true)
  have subtract : Executes (subtractLength (extra+3) (w 2) (w 4) (w 5) (w 6)) added
      (7*place+4) subtracted := by
    have run := subtractLength_executes (extra+3) (w 2) (w 4) (w 5) (w 6)
      (distinct (by decide)) (distinct (by decide)) (distinct (by decide)) (distinct (by decide)) added
      (by simp [added,incremented,w.injective.eq_iff,counterEmpty])
      (by simp [added,incremented,w.injective.eq_iff,workEmpty])
    have source : added (w 2)=List.replicate place true := by simp [added,incremented,w.injective.eq_iff,placeValue]
    have target : added (w 4)=List.replicate width true := by simp [added]
    simpa only [source,target,List.length_replicate,List.drop_replicate,added,Function.update_idem,subtracted] using run
  have dropOne : Executes (discard (w 4) 1) subtracted 2 (rightPrepared w store center width place) := by
    simpa only [subtracted,Function.update_self,Function.update_idem,List.drop_replicate,rightPrepared,incremented] using
      discard_executes (w 4) 1 subtracted
  have combined := copy.sequence (push.sequence (addWidth.sequence (subtract.sequence dropOne)))
  simpa +instances only [rightPrepare,ListPrograms.copyProgram,rightPrepareCost,
    show 5*center+2+1+(1+1+(5*width+2+1+(7*place+4+1+2)))=5*center+5*width+7*place+15 by omega] using combined

/-- When no room remains on the row, subtract a whole width; otherwise
retain the incremented identifier. Both branches are actual stack programs. -/
def rightFinish (extra : Nat) (w : RightWorkspace extra) : Routine (extra+5) :=
  sequence (branchUnary (w 4) (skip (extra+5))
    (subtractLength (extra+3) (w 1) (w 3) (w 5) (w 6))) (clear (w 4))

def rightIndex (center width place : Nat) : Nat :=
  if width-place-1=0 then center+1-width else center+1

def rightFinishCost (width place : Nat) :=
  (if width-place-1=0 then 7*width+5 else 3)+(width-place-1)+2

theorem rightFinish_executes (extra : Nat) (w : RightWorkspace extra) (center width place : Nat)
    (store : Fin (extra+7) → List Bool)
    (widthValue : store (w 1)=List.replicate width true)
    (remainderEmpty : store (w 4)=[]) (counterEmpty : store (w 5)=[]) (workEmpty : store (w 6)=[]) :
    Executes (rightFinish extra w) (rightPrepared w store center width place)
      (rightFinishCost width place)
      (Function.update store (w 3) (List.replicate (rightIndex center width place) true)) := by
  have distinct {a b : Fin 7} (different : a ≠ b) : w a ≠ w b := fun same => different (w.injective same)
  let prepared := rightPrepared w store center width place
  let selected := Function.update (Function.update store (w 3) (List.replicate (rightIndex center width place) true))
    (w 4) (List.replicate (width-place-1) true)
  have choice : Executes (branchUnary (w 4) (skip (extra+5))
      (subtractLength (extra+3) (w 1) (w 3) (w 5) (w 6))) prepared
      (if width-place-1=0 then 7*width+5 else 3) selected := by
    by_cases zero : width-place-1=0
    · have run := subtractLength_executes (extra+3) (w 1) (w 3) (w 5) (w 6)
        (distinct (by decide)) (distinct (by decide)) (distinct (by decide)) (distinct (by decide)) prepared
        (by simp [prepared,rightPrepared,w.injective.eq_iff,counterEmpty])
        (by simp [prepared,rightPrepared,w.injective.eq_iff,workEmpty])
      have source : prepared (w 1)=List.replicate width true := by simp [prepared,rightPrepared,w.injective.eq_iff,widthValue]
      have target : prepared (w 3)=List.replicate (center+1) true := by simp [prepared,rightPrepared,w.injective.eq_iff]
      have change : Function.update prepared (w 3) (List.replicate (center+1-width) true)=selected := by
        funext r
        by_cases a : r=w 3
        · subst r; simp [selected,rightIndex,zero,w.injective.eq_iff]
        · by_cases b : r=w 4
          · subst r; simp [selected,prepared,rightPrepared,w.injective.eq_iff]
          · simp [selected,prepared,rightPrepared,a,b]
      rw [source,target,List.length_replicate,List.drop_replicate,change] at run
      have branched := branchUnary_zero (w 4) (skip (extra+5))
        (subtractLength (extra+3) (w 1) (w 3) (w 5) (w 6)) prepared selected (7*width+4)
        (by simp [prepared,rightPrepared,zero]) run
      simpa only [zero,ite_true,show 1+(7*width+4)=7*width+5 by omega] using branched
    · obtain ⟨rest,nonzero⟩ := Nat.exists_eq_succ_of_ne_zero zero
      have same : prepared=selected := by simp only [prepared,selected,rightPrepared,rightIndex,zero,ite_false]
      have run := branchUnary_nonzero (w 4) (skip (extra+5))
        (subtractLength (extra+3) (w 1) (w 3) (w 5) (w 6)) prepared prepared (List.replicate rest true) 0
        (by simp [prepared,rightPrepared,nonzero,List.replicate_succ]) (skip_executes prepared)
      simpa only [zero,ite_false,same] using run
  have cleared : Executes (clear (w 4)) selected ((width-place-1)+1)
      (Function.update store (w 3) (List.replicate (rightIndex center width place) true)) := by
    have run := clear_executes (w 4) selected
    have value : selected (w 4)=List.replicate (width-place-1) true := by simp [selected]
    have result : Function.update selected (w 4) [] =
        Function.update store (w 3) (List.replicate (rightIndex center width place) true) := by
      funext r
      by_cases a : r=w 4
      · subst r; simp [selected,w.injective.eq_iff,remainderEmpty]
      · simp [selected,a]
    simpa only [value,List.length_replicate,result] using run
  have combined := choice.sequence cleared
  have cost : (if width-place-1=0 then 7*width+5 else 3)+1+(width-place-1+1)=rightFinishCost width place := by
    unfold rightFinishCost
    omega
  simpa only [rightFinish,prepared,cost] using combined

def rightRoutine (extra : Nat) (w : RightWorkspace extra) : Routine (extra+5) :=
  sequence (rightPrepare extra w) (rightFinish extra w)

theorem rightRoutine_executes (extra : Nat) (w : RightWorkspace extra) (center width place : Nat)
    (store : Fin (extra+7) → List Bool)
    (centerValue : store (w 0)=List.replicate center true)
    (widthValue : store (w 1)=List.replicate width true)
    (placeValue : store (w 2)=List.replicate place true)
    (outputEmpty : store (w 3)=[]) (remainderEmpty : store (w 4)=[])
    (counterEmpty : store (w 5)=[]) (workEmpty : store (w 6)=[]) :
    Executes (rightRoutine extra w) store
      (rightPrepareCost center width place+1+rightFinishCost width place)
      (Function.update store (w 3) (List.replicate (rightIndex center width place) true)) :=
  (rightPrepare_executes extra w center width place store centerValue widthValue placeValue outputEmpty
    remainderEmpty counterEmpty workEmpty).sequence
  (rightFinish_executes extra w center width place store widthValue remainderEmpty counterEmpty workEmpty)

theorem rightCost_bound (center width place : Nat) :
    rightPrepareCost center width place+1+rightFinishCost width place ≤ 5*center+13*width+7*place+23 := by
  unfold rightPrepareCost rightFinishCost
  split <;> omega

end Counting.External.CookLevin.StackGenerator
