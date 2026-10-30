import Counting.StackLexReadPair
import Counting.StackBranchNonempty

namespace Counting.StackMachine.Lexicographic
open Routine
set_option backward.isDefEq.respectTransparency false

def rejectUnresolved : Routine 14 := sequence (clear 3)
  (sequence (pushBit 3 false) (sequence (clear 2) (pushBit 2 false)))

def shortRight : Routine 14 := sequence (branchRead 2 rejectUnresolved (skip 14)) (clear 10)

def shortResult (store : Store 14) (unresolved answer : Bool) : Store 14 :=
  Function.update (Function.update (Function.update store 2 [false]) 3 [if unresolved then false else answer]) 10 []

private theorem rejectUnresolved_executes (store : Store 14) (answer : Bool)
    (openAt : store 2=[true]) (answerAt : store 3=[answer]) :
    Executes rejectUnresolved store 9 (Function.update (Function.update store 3 [false]) 2 [false]) := by
  have first := clear_executes (3:Fin 16) store
  rw [answerAt,List.length_singleton] at first
  let s1 := Function.update store 3 []
  have second := pushBit_executes (3:Fin 16) false s1
  have empty : s1 3=[] := by simp [s1]
  rw [empty] at second
  let s2 := Function.update s1 3 [false]
  have third := clear_executes (2:Fin 16) s2
  have opened : s2 2=[true] := by simp [s2,s1,openAt]
  rw [opened,List.length_singleton] at third
  let s3 := Function.update s2 2 []
  have fourth := pushBit_executes (2:Fin 16) false s3
  have erased : s3 2=[] := by simp [s3]
  rw [erased] at fourth
  simpa only [rejectUnresolved,s3,s2,s1,Function.update_idem] using first.sequence (second.sequence (third.sequence fourth))

/-- If the second key has ended first, its comparison result is false
unless an earlier unequal pair has already fixed the result. -/
theorem shortRight_executes (store : Store 14) (unresolved answer : Bool)
    (openAt : store 2=[unresolved]) (answerAt : store 3=[answer]) :
    Executes shortRight store ((store 10).length+(if unresolved then 14 else 5))
      (shortResult store unresolved answer) := by
  cases unresolved with
  | false =>
    have selected := branchRead_executes (2:Fin 16) rejectUnresolved (skip 14) false []
      store store 0 openAt (skip_executes store)
    have erase := clear_executes (10:Fin 16) store
    have final : Function.update store 10 []=shortResult store false answer := by
      simp [shortResult,←openAt,←answerAt]
    rw [final] at erase
    convert selected.sequence erase using 1 <;> first | rfl | (simp;omega)
  | true =>
    have selected := branchRead_executes (2:Fin 16) rejectUnresolved (skip 14) true [] store _ 9 openAt
      (rejectUnresolved_executes store answer openAt answerAt)
    let s1 := Function.update (Function.update store 3 [false]) 2 [false]
    have erase := clear_executes (10:Fin 16) s1
    have stream : s1 10=store 10 := by simp [s1]
    rw [stream] at erase
    have final : Function.update s1 10 []=shortResult store true answer := by
      funext r
      fin_cases r <;> simp [s1,shortResult]
    rw [final] at erase
    convert selected.sequence erase using 1 <;> first | rfl | (simp;omega)

end Counting.StackMachine.Lexicographic
