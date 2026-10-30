import Counting.StackAuditBalancePrepared
import Counting.StackDagClean
import Counting.StackRoutineClean

namespace Counting.StackMachine.AuditBalance
open Routine RealizabilityCheck
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

def balanceCleanup : List (Fin 50) := [22,34,35,42,44,49]

abbrev finishBalance : Routine 48 := clearRegisters balanceCleanup

def balanceCleanupBudget (anchor : Nat) (vista : Executable.Vista) (weights : Array Nat) : Nat :=
  6*((Encoding.vista.encode vista).length+((Encoding.array Encoding.natural).encode weights).length+
    (Encoding.sequence Encoding.node vista.nodes.toList++Encoding.natural.encode vista.bottom).length+
    vista.nodes.size+(anchor-1).size+(anchor-1+1).size+2)

/-- Erase both input words, the scan table and all counters. The Boolean
decision already occupies the sole output register. -/
theorem finishBalance_executes (anchor : Nat) (vista : Executable.Vista) (weights : Array Nat) :
    ∃ time ≤ balanceCleanupBudget anchor vista weights,
      Executes finishBalance (balanceDoneFile anchor vista weights) time
        (outputStore 48 [Executable.auditBalance vista weights anchor]) := by
  let store:=balanceDoneFile anchor vista weights
  let limit:=(Encoding.vista.encode vista).length+((Encoding.array Encoding.natural).encode weights).length+
    (Encoding.sequence Encoding.node vista.nodes.toList++Encoding.natural.encode vista.bottom).length+
    vista.nodes.size+(anchor-1).size+(anchor-1+1).size
  have bounded (i : Fin 50) (member : i∈balanceCleanup) : (store i).length ≤ limit := by
    simp only [balanceCleanup,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl|rfl|rfl <;>
      simp [store,balanceDoneFile,roundsSaved,balanceSaved,bankFile,massFile,limit,Encoding.bits_length] <;> omega
  obtain ⟨time,bounded,run⟩:=DagValidation.clear_selected_executes balanceCleanup store limit bounded
  have cleared : clearedStore balanceCleanup store=outputStore 48 [Executable.auditBalance vista weights anchor] := by
    funext i
    fin_cases i <;> simp [clearedStore,balanceCleanup,store,balanceDoneFile,roundsSaved,
      balanceSaved,bankFile,massFile,outputStore]
  rw [cleared] at run
  exact ⟨time,bounded,run⟩

end Counting.StackMachine.AuditBalance
