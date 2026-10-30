import Counting.StackAuditPropagationPrepared
import Counting.StackDagClean
import Counting.StackRoutineClean

namespace Counting.StackMachine.AuditPropagation
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

def propagationOutputWord (anchor : Nat) (vista : Executable.Vista) (values : Array Nat) : List Bool :=
  (Encoding.array Encoding.natural).encode (Executable.propagateWeights vista anchor values)

def propagationCleanup : List (Fin 44) := [1,17,34,36,40,42]

abbrev finishPropagation : Routine 42 := sequence (clearRegisters propagationCleanup) (move 41 35 1 43)

/-- Erase the surviving DAG, node counters, anchor and status, then move the
actual propagated array to the sole output register. -/
theorem finishPropagation_executes (anchor : Nat) (vista : Executable.Vista) (values : Array Nat) :
    ∃ time ≤ 10*((Encoding.vista.encode vista).length+
        (Encoding.sequence Encoding.node vista.nodes.toList++Encoding.natural.encode vista.bottom).length+
        2*vista.nodes.size+anchor.size+(propagationOutputWord anchor vista values).length+4),
      Executes finishPropagation (propagationDoneFile anchor vista values) time
        (outputStore 42 (propagationOutputWord anchor vista values)) := by
  let store := propagationDoneFile anchor vista values
  let table := Encoding.sequence Encoding.node vista.nodes.toList++Encoding.natural.encode vista.bottom
  let limit := (Encoding.vista.encode vista).length+table.length+2*vista.nodes.size+anchor.size+1
  have bounded (i : Fin 44) (member : i∈propagationCleanup) : (store i).length ≤ limit := by
    simp only [propagationCleanup,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl|rfl|rfl <;>
      simp [store,propagationDoneFile,limit,table,Encoding.bits_length] <;> omega
  obtain ⟨clearTime,clearBound,a⟩ := DagValidation.clear_selected_executes propagationCleanup store limit bounded
  let word := propagationOutputWord anchor vista values
  let cleaned : Store 42 := fun i=>if i=35 then word else []
  have cleared : clearedStore propagationCleanup store=cleaned := by
    funext i
    fin_cases i <;> simp [clearedStore,propagationCleanup,store,propagationDoneFile,cleaned,word,propagationOutputWord]
  rw [cleared] at a
  have b := move_executes 41 (35:Fin 44) 1 43 (by decide) (by decide) (by decide) cleaned (by simp [cleaned])
  have source : cleaned 35=word := by simp [cleaned]
  have target : cleaned 1=[] := by simp [cleaned]
  rw [source,target,List.append_nil] at b
  have result : Function.update (Function.update cleaned 1 word) 35 []=outputStore 42 word := by
    funext i
    by_cases i1 : i=1 <;> by_cases i35 : i=35 <;> simp [cleaned,outputStore,i1,i35]
  rw [result] at b
  refine ⟨_,?_,a.sequence b⟩
  change clearTime ≤ 6*(limit+2) at clearBound
  dsimp only [limit,table] at clearBound
  dsimp only [word]
  omega

end Counting.StackMachine.AuditPropagation
