import Counting.StackAuditBalanceRound
import Counting.AuditBalanceRoundsSpec

namespace Counting.StackMachine.AuditBalance
open Routine RealizabilityCheck
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000

abbrev roundsLoop : Routine 48 := forEach 48 roundItem

def roundsBudget (vista : Executable.Vista) (weights : Array Nat) : Nat → Nat → Nat
  | _,0 => 1
  | start,count+1 => roundBudget vista weights start+2+roundsBudget vista weights (start+1) count

def roundsSaved (saved : Fin 8 → List Bool) (start count : Nat) : Fin 8 → List Bool :=
  Function.update (Function.update saved 2 (start+count).bits) 6 []

/-- Execute every balance round, charging the physical level scans and
both loop transitions. No weights or labels are supplied by an oracle. -/
theorem roundsLoop_executes (vista : Executable.Vista) (weights : Array Nat)
    (valid : vista.valid=true) (length : weights.size=vista.nodes.size)
    (start count : Nat) (accepted : Bool) (tail : List Bool) (saved : Fin 8 → List Bool)
    (table : saved 0=Encoding.sequence Encoding.node vista.nodes.toList++Encoding.natural.encode vista.bottom)
    (indexEmpty : saved 1=[]) (query : saved 2=start.bits) (flag : saved 3=[])
    (counterEmpty : saved 4=[]) (scratch : saved 5=[])
    (counter : saved 6=List.replicate count true) (nodeCount : saved 7=List.replicate vista.nodes.size true) :
    ∃ time ≤ roundsBudget vista weights start count,
      Executes roundsLoop
        (bankFile (Encoding.vista.encode vista) ((Encoding.array Encoding.natural).encode weights)
          (start+1).bits [] (accepted::tail) saved) time
        (bankFile (Encoding.vista.encode vista) ((Encoding.array Encoding.natural).encode weights)
          (start+count+1).bits []
          ((accepted && Executable.auditBalanceRounds vista weights start count)::tail)
          (roundsSaved saved start count)) := by
  induction count generalizing start accepted saved with
  | zero =>
    let store := bankFile (Encoding.vista.encode vista) ((Encoding.array Encoding.natural).encode weights)
      (start+1).bits [] (accepted::tail) saved
    have empty : store 48=[] := by simp [store,bankFile,counter]
    obtain ⟨ran,halted⟩ := repeat_empty (48:Fin 50) roundItem store empty
    have restored : roundsSaved saved start 0=saved := by
      funext i
      by_cases two : i=2 <;> by_cases six : i=6 <;>
        simp [roundsSaved,two,six,query,counter]
    refine ⟨1,by simp [roundsBudget],⟨1,store⟩,ran,halted,?_⟩
    simp only [Executable.auditBalanceRounds_zero,Bool.and_true,restored,Nat.add_zero]
    rfl
  | succ count ih =>
    let store := bankFile (Encoding.vista.encode vista) ((Encoding.array Encoding.natural).encode weights)
      (start+1).bits [] (accepted::tail) saved
    let consumed := Function.update saved 6 (List.replicate count true)
    have popped : Function.update store 48 (List.replicate count true)=
        bankFile (Encoding.vista.encode vista) ((Encoding.array Encoding.natural).encode weights)
          (start+1).bits [] (accepted::tail) consumed :=
      bankFile_saved_update _ _ _ _ _ saved 6 _
    obtain ⟨bodyTime,bodyBound,finishBody,bodyRun,bodyHalt,bodyStore⟩ :=
      roundItem_executes vista weights valid length start accepted tail consumed
        (by simp [consumed,table]) (by simp [consumed,indexEmpty])
        (by simp [consumed,query]) (by simp [consumed,flag])
        (by simp [consumed,counterEmpty]) (by simp [consumed,scratch])
        (by simp [consumed,nodeCount])
    let next := Function.update consumed 2 (start+1).bits
    obtain ⟨tailTime,tailBound,finishTail,tailRun,tailHalt,tailStore⟩ :=
      ih (start+1) (accepted && Executable.auditBalanceLevel vista weights start) next
        (by simp [next,consumed,table]) (by simp [next,consumed,indexEmpty])
        (by simp [next]) (by simp [next,consumed,flag])
        (by simp [next,consumed,counterEmpty]) (by simp [next,consumed,scratch])
        (by simp [next,consumed]) (by simp [next,consumed,nodeCount])
    have firstRun := repeat_iteration (48:Fin 50) roundItem store true (List.replicate count true)
      (by simp [store,bankFile,counter,List.replicate_succ]) bodyTime finishBody
      (by rw [popped];exact bodyRun) bodyHalt
    have savedEq : roundsSaved next (start+1) count=roundsSaved saved start (count+1) := by
      funext i
      by_cases two : i=2 <;> by_cases six : i=6 <;>
        simp [roundsSaved,next,consumed,two,six,Nat.add_comm,Nat.add_left_comm]
    have finalStore :
        bankFile (Encoding.vista.encode vista) ((Encoding.array Encoding.natural).encode weights)
          (start+1+count+1).bits []
          (((accepted && Executable.auditBalanceLevel vista weights start) &&
            Executable.auditBalanceRounds vista weights (start+1) count)::tail)
          (roundsSaved next (start+1) count)=
        bankFile (Encoding.vista.encode vista) ((Encoding.array Encoding.natural).encode weights)
          (start+(count+1)+1).bits []
          ((accepted && Executable.auditBalanceRounds vista weights start (count+1))::tail)
          (roundsSaved saved start (count+1)) := by
      rw [savedEq]
      simp only [Executable.auditBalanceRounds_succ,Bool.and_assoc]
      congr 2
      omega
    refine ⟨bodyTime+2+tailTime,?_,finishTail,?_,tailHalt,tailStore.trans finalStore⟩
    · simpa only [roundsBudget] using Nat.add_le_add (Nat.add_le_add_right bodyBound 2) tailBound
    · rw [Machine.run_add,firstRun,Option.bind_some,bodyStore]
      exact tailRun

end Counting.StackMachine.AuditBalance
