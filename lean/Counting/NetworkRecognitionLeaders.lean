import Counting.StackEncodingBranch
import Counting.StackRoutineBasic

namespace Counting.StackMachine.NetworkRecognition
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false

/-- Consume one explicit leader bit, retaining its value and counting true
bits. Only the explicit number of agents is represented in unary. -/
def leaderItem : Routine 2 := branchRoutine 0
  (sequence (pushBit 2 true) (pushBit 3 true)) (pushBit 2 false)

def leaderItemStore (store : Store 2) (bit : Bool) (suffix : List Bool) : Store 2 :=
  Function.update (Function.update (Function.update store 0 suffix) 2 (bit::store 2))
    3 (if bit then true::store 3 else store 3)

theorem leaderItem_executes (store : Store 2) (bit : Bool) (suffix : List Bool)
    (source : store 0=bit::suffix) :
    Executes leaderItem store (2+2*(if bit then 1 else 0))
      (leaderItemStore store bit suffix) := by
  cases bit with
  | false =>
    have result := branch_executes_false (0:Fin 4)
      (sequence (pushBit 2 true) (pushBit 3 true)) (pushBit 2 false)
      store _ suffix 1 source (pushBit_executes 2 false (Function.update store 0 suffix))
    have final : Function.update (Function.update store 0 suffix) 2 (false::store 2)=
        leaderItemStore store false suffix := by
      funext i
      fin_cases i <;> simp [leaderItemStore]
    simp only [Function.update_of_ne (by decide : (2:Fin 4)≠0)] at result
    rw [final] at result
    exact result
  | true =>
    have first := pushBit_executes (2:Fin 4) true (Function.update store 0 suffix)
    have second := pushBit_executes (3:Fin 4) true
      (Function.update (Function.update store 0 suffix) 2 (true::store 2))
    have result := branch_executes_true (0:Fin 4)
      (sequence (pushBit 2 true) (pushBit 3 true)) (pushBit 2 false)
      store _ suffix 3 source (by simpa using first.sequence second)
    simpa [leaderItem,leaderItemStore] using result

def leaderScan : Routine 2 := forEach 1 leaderItem

def leaderScanStore (store : Store 2) (values suffix : List Bool) : Store 2 :=
  Function.update (Function.update (Function.update (Function.update store 0 suffix) 1 [])
    2 (values.reverse++store 2)) 3 (List.replicate (values.count true) true++store 3)

/-- Exact stack-step count for all leader bits, preserving every register
outside the four declared roles. The suffix is untouched. -/
theorem leaderScan_executes (values suffix : List Bool) (store : Store 2)
    (source : store 0=values++suffix) (counter : store 1=List.replicate values.length true) :
    Executes leaderScan store (4*values.length+2*values.count true+1)
      (leaderScanStore store values suffix) := by
  induction values generalizing store with
  | nil =>
    obtain ⟨ran,halted⟩ := repeat_empty (1:Fin 4) leaderItem store (by simpa using counter)
    have final : leaderScanStore store [] suffix=store := by
      funext i
      fin_cases i <;> simp_all [leaderScanStore]
    exact ⟨⟨1,store⟩,ran,halted,final.symm⟩
  | cons bit values ih =>
    let consumed := Function.update store 1 (List.replicate values.length true)
    obtain ⟨body,bodyRun,bodyHalted,bodyStore⟩ := leaderItem_executes consumed bit (values++suffix)
      (by simpa [consumed] using source)
    let middle := leaderItemStore consumed bit (values++suffix)
    obtain ⟨finish,tailRun,tailHalted,tailStore⟩ := ih middle
      (by simp [middle,leaderItemStore]) (by simp [middle,leaderItemStore,consumed])
    have firstRun := repeat_iteration (1:Fin 4) leaderItem store true
      (List.replicate values.length true) (by simpa only [List.length_cons,List.replicate_succ] using counter)
      (2+2*(if bit then 1 else 0)) body bodyRun bodyHalted
    change Machine.run (step leaderScan.program) _ _ = _ at firstRun
    have final : leaderScanStore middle values suffix=leaderScanStore store (bit::values) suffix := by
      funext i
      fin_cases i <;> cases bit <;>
        simp [leaderScanStore,middle,leaderItemStore,consumed,List.replicate_succ',List.append_assoc]
    have total : 4*(bit::values).length+2*(bit::values).count true+1=
        (2+2*(if bit then 1 else 0)+2)+(4*values.length+2*values.count true+1) := by
      cases bit <;> simp <;> omega
    refine ⟨finish,?_,tailHalted,tailStore.trans final⟩
    rw [total,Machine.run_add,firstRun,Option.bind_some,bodyStore]
    exact tailRun

theorem leaderScan_cost_le (values : List Bool) :
    4*values.length+2*values.count true+1 ≤ 6*values.length+1 := by
  have := List.count_le_length (a:=true) (l:=values)
  omega

end Counting.StackMachine.NetworkRecognition
