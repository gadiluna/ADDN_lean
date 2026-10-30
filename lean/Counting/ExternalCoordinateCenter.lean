import Counting.StackPolynomialLength

namespace Counting.External.CookLevin.StackGenerator
open StackMachine StackMachine.Routine

/-- Roles: time, width, place, center identifier, copied time, scratch.
Compute `time*width+place` with both operands preserved. -/
def centerRoutine (extra : Nat) (w : PolynomialWorkspace extra) : Routine (extra+4) :=
  sequence (ofProgram (ListPrograms.copyProgram (extra+3) (w 0) (w 4) (w 5)))
    (sequence (repeatedCopy (extra+3) (w 1) (w 4) (w 3) (w 5))
      (ofProgram (ListPrograms.copyProgram (extra+3) (w 2) (w 3) (w 5))))

def centerCost (time width place : Nat) : Nat := (5*width+9)*time+5*place+7

theorem centerRoutine_executes (extra : Nat) (w : PolynomialWorkspace extra) (time width place : Nat)
    (store : Fin (extra+6) → List Bool)
    (timeValue : store (w 0)=List.replicate time true)
    (widthValue : store (w 1)=List.replicate width true)
    (placeValue : store (w 2)=List.replicate place true)
    (centerEmpty : store (w 3)=[]) (counterEmpty : store (w 4)=[]) (workEmpty : store (w 5)=[]) :
    Executes (centerRoutine extra w) store (centerCost time width place)
      (Function.update store (w 3) (List.replicate (time*width+place) true)) := by
  have distinct {a b : Fin 6} (different : a ≠ b) : w a ≠ w b := fun same => different (w.injective same)
  let copied := Function.update store (w 4) (List.replicate time true)
  have copy : Executes (ofProgram (ListPrograms.copyProgram (extra+3) (w 0) (w 4) (w 5))) store
      (5*time+2) copied := by
    simpa +instances only [ListPrograms.copyProgram,timeValue,counterEmpty,List.length_replicate,List.append_nil,copied] using
      copy_executes (extra+3) (w 0) (w 4) (w 5)
        (distinct (by decide)) (distinct (by decide)) (distinct (by decide)) store workEmpty
  have multiplied := unary_multiply_executes (extra+3) (w 1) (w 4) (w 3) (w 5)
    (distinct (by decide)) (distinct (by decide)) (distinct (by decide))
    (distinct (by decide)) (distinct (by decide)) (distinct (by decide)) width time copied
    (by simp [copied,w.injective.eq_iff,widthValue]) (by simp [copied])
    (by simp [copied,w.injective.eq_iff,workEmpty])
  let middle := Function.update store (w 3) (List.replicate (time*width) true)
  have multipliedStore : Function.update (Function.update copied (w 4) []) (w 3)
      (List.replicate (time*width) true++copied (w 3)) = middle := by
    funext register
    by_cases result : register=w 3
    · subst register; simp [middle,copied,w.injective.eq_iff,centerEmpty]
    · by_cases counter : register=w 4
      · subst register; simp [middle,copied,w.injective.eq_iff,counterEmpty]
      · simp [middle,copied,result,counter]
  rw [multipliedStore] at multiplied
  have finalCopy := copy_executes (extra+3) (w 2) (w 3) (w 5)
    (distinct (by decide)) (distinct (by decide)) (distinct (by decide)) middle
    (by simp [middle,w.injective.eq_iff,workEmpty])
  have last : Executes (ofProgram (ListPrograms.copyProgram (extra+3) (w 2) (w 3) (w 5))) middle
      (5*place+2) (Function.update store (w 3) (List.replicate (time*width+place) true)) := by
    have source : middle (w 2)=List.replicate place true := by simp [middle,w.injective.eq_iff,placeValue]
    have target : middle (w 3)=List.replicate (time*width) true := by simp [middle]
    simpa +instances only [ListPrograms.copyProgram,source,target,List.length_replicate,
      ← List.replicate_add,middle,Function.update_idem,Nat.add_comm place] using finalCopy
  have combined := copy.sequence (multiplied.sequence last)
  have cost : 5*time+2+1+(((5*width+4)*time+1)+1+(5*place+2)) = centerCost time width place := by
    unfold centerCost
    ring
  rw [cost] at combined
  exact combined

theorem centerCost_bound (time width place bound : Nat) (ht : time≤bound) (hw : width≤bound) (hp : place≤bound) :
    centerCost time width place ≤ 26*(bound+1)^2 := by
  have product := Nat.mul_le_mul ht hw
  unfold centerCost
  nlinarith

end Counting.External.CookLevin.StackGenerator
