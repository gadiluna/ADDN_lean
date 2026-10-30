import Counting.StackFrameMove

namespace Counting.StackMachine.FieldAccess
open Routine

def frontMany : Nat → List Bool → List Bool
  | 0, _ => []
  | count+1, input => frameFront input++frontMany count (skipRest input)

def moveManyCost : Nat → List Bool → Nat
  | 0, _ => 1
  | count+1, input => moveCost input+2+moveManyCost count (skipRest input)

theorem frontMany_append (count : Nat) (input : List Bool) :
    frontMany count input++skipMany count input=input := by
  induction count generalizing input with
  | zero => rfl
  | succ count ih => rw [frontMany,skipMany,List.append_assoc,ih,frameFront_append]

theorem frontMany_length (count : Nat) (input : List Bool) :
    (frontMany count input).length ≤ input.length := by
  have split := congrArg List.length (frontMany_append count input)
  simp only [List.length_append] at split
  omega

theorem moveManyCost_le (count : Nat) (input : List Bool) :
    moveManyCost count input≤2*input.length+3*count+1 := by
  induction count generalizing input with
  | zero => simp [moveManyCost]
  | succ count ih =>
      have next := ih (skipRest input)
      have current := moveCost_amortized input
      simp only [moveManyCost]
      omega

def moveBody (source target : Fin (extra+2)) (store : Store extra) : Store extra :=
  Function.update (Function.update store source (skipRest (store source))) target
    ((frameFront (store source)).reverse++store target)

theorem moveIteration_source (source counter target : Fin (extra+2))
    (sc : source≠counter) (st : source≠target) (store : Store extra) :
    iteration counter (moveBody source target) store source=skipRest (store source) := by
  simp [iteration,moveBody,consume,sc,st]

theorem moveIteration_target (source counter target : Fin (extra+2))
    (sc : source≠counter) (tc : target≠counter) (store : Store extra) :
    iteration counter (moveBody source target) store target=(frameFront (store source)).reverse++store target := by
  simp [iteration,moveBody,consume,sc,tc]

theorem moveIteration_counter (source counter target : Fin (extra+2))
    (sc : source≠counter) (tc : target≠counter) (store : Store extra) :
    iteration counter (moveBody source target) store counter=(store counter).tail := by
  simp [iteration,moveBody,consume,Ne.symm sc,Ne.symm tc]

theorem moveIteration_other (source counter target r : Fin (extra+2))
    (rs : r≠source) (rc : r≠counter) (rt : r≠target) (store : Store extra) :
    iteration counter (moveBody source target) store r=store r := by
  simp [iteration,moveBody,consume,rs,rc,rt]

theorem move_iteration (source counter target : Fin (extra+2))
    (sc : source≠counter) (st : source≠target) (tc : target≠counter)
    (count : Nat) (store : Store extra) :
    (iteration counter (moveBody source target))^[count] store =
      Function.update (Function.update (Function.update store counter ((store counter).drop count))
        source (skipMany count (store source))) target ((frontMany count (store source)).reverse++store target) := by
  induction count generalizing store with
  | zero => simp [frontMany,skipMany]
  | succ count ih =>
      rw [Function.iterate_succ_apply,ih,moveIteration_source source counter target sc st,
        moveIteration_counter source counter target sc tc,moveIteration_target source counter target sc tc]
      funext r
      by_cases atTarget : r=target
      · subst r
        simp [frontMany,List.reverse_append,List.append_assoc]
      · by_cases atSource : r=source
        · subst r; simp [st,skipMany]
        · by_cases atCounter : r=counter
          · subst r; simp [Ne.symm sc,Ne.symm tc,List.drop_tail]
          · simp [Function.update_of_ne atTarget,Function.update_of_ne atSource,
              Function.update_of_ne atCounter,moveIteration_other source counter target r atSource atCounter atTarget]

theorem move_time (source counter target : Fin (extra+2))
    (sc : source≠counter) (st : source≠target)
    (count : Nat) (store : Store extra) :
    loopTime counter (moveBody source target) (fun state=>moveCost (state source)) count store=
      moveManyCost count (store source) := by
  induction count generalizing store with
  | zero => rfl
  | succ count ih =>
      rw [loopTime,ih,moveIteration_source source counter target sc st]
      simp [consume,sc,moveManyCost]

theorem moveMany_executes (extra : Nat) (source counter target : Fin (extra+2))
    (sc : source≠counter) (st : source≠target) (tc : target≠counter) (store : Store extra) :
    Executes (forEach counter (ofProgram (moveProgram extra source target))) store
      (moveManyCost (store counter).length (store source))
      (Function.update (Function.update (Function.update store counter [])
        source (skipMany (store counter).length (store source)))
        target ((frontMany (store counter).length (store source)).reverse++store target)) := by
  have run := forEach_executes counter (ofProgram (moveProgram extra source target)) (moveBody source target)
    (fun state=>moveCost (state source)) (fun state=>move_executes extra source target st state)
    (fun state=>by simp [moveBody,Ne.symm sc,Ne.symm tc]) (store counter).length store rfl
  rw [move_time source counter target sc st,move_iteration source counter target sc st tc] at run
  simpa only [List.drop_length] using run

end Counting.StackMachine.FieldAccess
