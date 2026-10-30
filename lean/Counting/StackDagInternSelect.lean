import Counting.StackReadBranch
import Counting.StackRoutineBasic

namespace Counting.StackMachine.DagUpdate.Intern
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false

def selectMatch : Routine 30 :=
  branchRoutine 20 (sequence (clear 19) (pushBit 19 true))
    (branchRead 19 (skip 30) (pushBit 18 true))

def selected (store : Store 30) (found matched : Bool) : Store 30 :=
  Function.update (Function.update (Function.update store 20 []) 19 [found || matched]) 18
    (if found || matched then store 18 else true::store 18)

theorem selectMatch_executes (store : Store 30) (found matched : Bool)
    (foundAt : store 19=[found]) (matchedAt : store 20=[matched]) :
    ∃ time ≤ 5, Executes selectMatch store time (selected store found matched) := by
  let ready := Function.update store 20 []
  cases matched with
  | true =>
    have cleared := clear_executes (19:Fin 32) ready
    have value : ready 19=[found] := by simp [ready,foundAt]
    rw [value] at cleared
    have pushed := pushBit_executes (19:Fin 32) true (Function.update ready 19 [])
    simp only [Function.update_self,Function.update_idem] at pushed
    have ran := branch_executes_true (20:Fin 32)
      (sequence (clear 19) (pushBit 19 true)) (branchRead 19 (skip 30) (pushBit 18 true))
      store (Function.update ready 19 [true]) [] 4 matchedAt (cleared.sequence pushed)
    have final : selected store found true=Function.update ready 19 [true] := by
      funext r
      fin_cases r <;> simp [selected,ready]
    exact ⟨5,by decide,by simpa only [selectMatch,final] using ran⟩
  | false =>
    have condition : ready 19=[found] := by simp [ready,foundAt]
    cases found with
    | true =>
      have body := branchRead_executes (19:Fin 32) (skip 30) (pushBit 18 true)
        true [] ready ready 0 condition (skip_executes ready)
      have ran := branch_executes_false (20:Fin 32)
        (sequence (clear 19) (pushBit 19 true)) (branchRead 19 (skip 30) (pushBit 18 true))
        store ready [] 3 matchedAt body
      have final : selected store true false=ready := by
        simp only [selected,Bool.true_or,ite_true]
        have eq19 : Function.update store 20 [] 19=[true] := by simp [foundAt]
        rw [←eq19,Function.update_eq_self]
        simp [ready]
      exact ⟨4,by decide,by simpa only [selectMatch,final] using ran⟩
    | false =>
      have body := branchRead_executes (19:Fin 32) (skip 30) (pushBit 18 true)
        false [] ready (Function.update ready 18 (true::ready 18)) 1 condition
        (pushBit_executes (18:Fin 32) true ready)
      have ran := branch_executes_false (20:Fin 32)
        (sequence (clear 19) (pushBit 19 true)) (branchRead 19 (skip 30) (pushBit 18 true))
        store (Function.update ready 18 (true::ready 18)) [] 4 matchedAt body
      have final : selected store false false=Function.update ready 18 (true::ready 18) := by
        simp only [selected,Bool.false_or]
        have eq19 : Function.update store 20 [] 19=[false] := by simp [foundAt]
        rw [←eq19,Function.update_eq_self]
        simp [ready]
      exact ⟨5,by decide,by simpa only [selectMatch,final] using ran⟩

end Counting.StackMachine.DagUpdate.Intern
