import Counting.StackReadBranch
import Counting.StackRoutineMove

namespace Counting.StackMachine.Lexicographic
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false

def keepAnswer : Routine 6 := sequence (clear 4) (clear 5)
def replaceAnswer : Routine 6 := sequence (clear 3)
  (sequence (move 5 5 3 6) (sequence (clear 2) (pushBit 2 false)))
def firstDifference : Routine 6 := branchRoutine 4 (clear 5) replaceAnswer
def settle : Routine 6 := branchRead 2 firstDifference keepAnswer

def settleCost (unresolved equal : Bool) : Nat := if unresolved then (if equal then 6 else 22) else 8

def settled (store : Store 6) (unresolved answer equal lessEqual : Bool) : Store 6 :=
  Function.update (Function.update (Function.update (Function.update store 2 [unresolved && equal])
    3 [if unresolved && !equal then lessEqual else answer]) 4 []) 5 []

private theorem replaceAnswer_executes (store : Store 6) (answer lessEqual : Bool)
    (openAt : store 2=[true]) (answerAt : store 3=[answer]) (lessAt : store 5=[lessEqual])
    (empty : store 6=[]) :
    Executes replaceAnswer store 18
      (Function.update (Function.update (Function.update store 3 [lessEqual]) 5 []) 2 [false]) := by
  have erase := clear_executes (3:Fin 8) store
  rw [answerAt,List.length_singleton] at erase
  let erased := Function.update store 3 []
  have moving := move_executes 5 (5:Fin 8) 3 6 (by decide) (by decide) (by decide) erased
    (by simp [erased,empty])
  have operand : erased 5=[lessEqual] := by simp [erased,lessAt]
  have output : erased 3=[] := by simp [erased]
  rw [operand,output,List.append_nil,List.length_singleton] at moving
  let moved := Function.update (Function.update erased 3 [lessEqual]) 5 []
  have close := clear_executes (2:Fin 8) moved
  have stillOpen : moved 2=[true] := by simp [moved,erased,openAt]
  rw [stillOpen,List.length_singleton] at close
  let closed := Function.update moved 2 []
  have mark := pushBit_executes (2:Fin 8) false closed
  have closedAt : closed 2=[] := by simp [closed]
  rw [closedAt] at mark
  have final : Function.update closed 2 [false]=
      Function.update (Function.update (Function.update store 3 [lessEqual]) 5 []) 2 [false] := by
    simp only [closed,moved,erased,Function.update_idem]
  rw [final] at mark
  exact erase.sequence (moving.sequence (close.sequence mark))

/-- Once a difference has decided the lexicographic answer, later pairs
cannot change it. All four flags are manipulated by actual instructions. -/
theorem settle_executes (store : Store 6) (unresolved answer equal lessEqual : Bool)
    (openAt : store 2=[unresolved]) (answerAt : store 3=[answer])
    (equalAt : store 4=[equal]) (lessAt : store 5=[lessEqual]) (empty : store 6=[]) :
    Executes settle store (settleCost unresolved equal) (settled store unresolved answer equal lessEqual) := by
  cases unresolved with
  | false =>
    have eraseEqual := clear_executes (4:Fin 8) store
    rw [equalAt,List.length_singleton] at eraseEqual
    let first := Function.update store 4 []
    have eraseLess := clear_executes (5:Fin 8) first
    have lastAt : first 5=[lessEqual] := by simp [first,lessAt]
    rw [lastAt,List.length_singleton] at eraseLess
    have final : Function.update first 5 []=settled store false answer equal lessEqual := by
      funext r
      by_cases r2 : r=2 <;> by_cases r3 : r=3 <;> by_cases r4 : r=4 <;> by_cases r5 : r=5 <;>
        simp [settled,first,r2,r3,r4,r5,openAt,answerAt]
    rw [final] at eraseLess
    exact branchRead_executes (2:Fin 8) firstDifference keepAnswer false [] store _ 5 openAt
      (eraseEqual.sequence eraseLess)
  | true =>
    cases equal with
    | true =>
      let consumed := Function.update store 4 []
      have erase := clear_executes (5:Fin 8) consumed
      have less : consumed 5=[lessEqual] := by simp [consumed,lessAt]
      rw [less,List.length_singleton] at erase
      have final : Function.update consumed 5 []=settled store true answer true lessEqual := by
        funext r
        by_cases r2 : r=2 <;> by_cases r3 : r=3 <;> by_cases r4 : r=4 <;> by_cases r5 : r=5 <;>
          simp [settled,consumed,r2,r3,r4,r5,openAt,answerAt]
      rw [final] at erase
      have chosen := branch_executes_true (4:Fin 8) (clear 5) replaceAnswer store _ [] 2 equalAt erase
      exact branchRead_executes (2:Fin 8) firstDifference keepAnswer true [] store _ 3 openAt chosen
    | false =>
      let consumed := Function.update store 4 []
      have replace := replaceAnswer_executes consumed answer lessEqual
        (by simp [consumed,openAt]) (by simp [consumed,answerAt])
        (by simp [consumed,lessAt]) (by simp [consumed,empty])
      have final : Function.update (Function.update (Function.update consumed 3 [lessEqual]) 5 []) 2 [false]=
          settled store true answer false lessEqual := by
        funext r
        by_cases r2 : r=2 <;> by_cases r3 : r=3 <;> by_cases r4 : r=4 <;> by_cases r5 : r=5 <;>
          simp [settled,consumed,r2,r3,r4,r5]
      rw [final] at replace
      have chosen := branch_executes_false (4:Fin 8) (clear 5) replaceAnswer store _ [] 18 equalAt replace
      exact branchRead_executes (2:Fin 8) firstDifference keepAnswer true [] store _ 19 openAt chosen

theorem settleCost_le (unresolved equal : Bool) : settleCost unresolved equal ≤ 22 := by
  cases unresolved <;> cases equal <;> decide

end Counting.StackMachine.Lexicographic
