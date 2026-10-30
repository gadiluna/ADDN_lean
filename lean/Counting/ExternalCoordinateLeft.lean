import Counting.ExternalCoordinateCenter
import Counting.StackUnaryBranch
import Counting.StackRoutineFixedPrefix

namespace Counting.External.CookLevin.StackGenerator
open StackMachine StackMachine.Routine

/-- Roles: center, width, place, output, unused, scratch. The place-zero
branch performs the ring wrap, while preserving all three source counters. -/
def leftRoutine (extra : Nat) (w : PolynomialWorkspace extra) : Routine (extra+4) :=
  sequence (ofProgram (ListPrograms.copyProgram (extra+3) (w 0) (w 3) (w 5)))
    (branchUnary (w 2) (discard (w 3) 1)
      (sequence (ofProgram (ListPrograms.copyProgram (extra+3) (w 1) (w 3) (w 5))) (discard (w 3) 1)))

def leftIndex (center width place : Nat) : Nat := if place=0 then center+width-1 else center-1

def leftCost (center width place : Nat) : Nat := 5*center+3+(if place=0 then 5*width+6 else 5)

theorem leftRoutine_executes (extra : Nat) (w : PolynomialWorkspace extra) (center width place : Nat)
    (store : Fin (extra+6) → List Bool)
    (centerValue : store (w 0)=List.replicate center true)
    (widthValue : store (w 1)=List.replicate width true)
    (placeValue : store (w 2)=List.replicate place true)
    (outputEmpty : store (w 3)=[]) (workEmpty : store (w 5)=[]) :
    Executes (leftRoutine extra w) store (leftCost center width place)
      (Function.update store (w 3) (List.replicate (leftIndex center width place) true)) := by
  have distinct {a b : Fin 6} (different : a ≠ b) : w a ≠ w b := fun same => different (w.injective same)
  let copied := Function.update store (w 3) (List.replicate center true)
  have copiedRun : Executes (ofProgram (ListPrograms.copyProgram (extra+3) (w 0) (w 3) (w 5))) store
      (5*center+2) copied := by
    simpa +instances only [ListPrograms.copyProgram,centerValue,outputEmpty,List.length_replicate,List.append_nil,copied] using
      copy_executes (extra+3) (w 0) (w 3) (w 5)
        (distinct (by decide)) (distinct (by decide)) (distinct (by decide)) store workEmpty
  have choice : Executes (branchUnary (w 2) (discard (w 3) 1)
      (sequence (ofProgram (ListPrograms.copyProgram (extra+3) (w 1) (w 3) (w 5))) (discard (w 3) 1))) copied
      (if place=0 then 5*width+6 else 5)
      (Function.update store (w 3) (List.replicate (leftIndex center width place) true)) := by
    cases place with
    | zero =>
        let filled := Function.update store (w 3) (List.replicate (center+width) true)
        have added : Executes (ofProgram (ListPrograms.copyProgram (extra+3) (w 1) (w 3) (w 5))) copied
            (5*width+2) filled := by
          have run := copy_executes (extra+3) (w 1) (w 3) (w 5)
            (distinct (by decide)) (distinct (by decide)) (distinct (by decide)) copied
            (by simp [copied,w.injective.eq_iff,workEmpty])
          have source : copied (w 1)=List.replicate width true := by simp [copied,w.injective.eq_iff,widthValue]
          have target : copied (w 3)=List.replicate center true := by simp [copied]
          simpa +instances only [ListPrograms.copyProgram,source,target,List.length_replicate,
            ← List.replicate_add,copied,Function.update_idem,Nat.add_comm width,filled] using run
        have dropped : Executes (discard (w 3) 1) filled 2
            (Function.update store (w 3) (List.replicate (center+width-1) true)) := by
          simpa only [filled,Function.update_self,Function.update_idem,List.drop_replicate] using discard_executes (w 3) 1 filled
        have run := branchUnary_zero (w 2) (discard (w 3) 1)
          (sequence (ofProgram (ListPrograms.copyProgram (extra+3) (w 1) (w 3) (w 5))) (discard (w 3) 1))
          copied _ ((5*width+2)+1+2) (by simp [copied,w.injective.eq_iff,placeValue]) (added.sequence dropped)
        simpa only [leftIndex,ite_true,show 1+(5*width+2+1+2)=5*width+6 by omega] using run
    | succ place =>
        have dropped : Executes (discard (w 3) 1) copied 2
            (Function.update store (w 3) (List.replicate (center-1) true)) := by
          simpa only [copied,Function.update_self,Function.update_idem,List.drop_replicate] using discard_executes (w 3) 1 copied
        have run := branchUnary_nonzero (w 2) (discard (w 3) 1)
          (sequence (ofProgram (ListPrograms.copyProgram (extra+3) (w 1) (w 3) (w 5))) (discard (w 3) 1))
          copied _ (List.replicate place true) 2
          (by simp [copied,w.injective.eq_iff,placeValue,List.replicate_succ]) dropped
        simpa only [leftIndex,Nat.succ_ne_zero,ite_false] using run
  have combined := copiedRun.sequence choice
  simpa +instances only [ListPrograms.copyProgram,leftRoutine,leftCost,show 5*center+2+1=5*center+3 by omega] using combined

theorem leftCost_bound (center width place : Nat) : leftCost center width place ≤ 5*center+5*width+9 := by
  unfold leftCost
  split <;> omega

end Counting.External.CookLevin.StackGenerator
