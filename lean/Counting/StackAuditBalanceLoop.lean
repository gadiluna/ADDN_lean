import Counting.StackAuditBalanceItem

namespace Counting.StackMachine.AuditBalance
open Routine RealizabilityCheck
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000

def rangeCheck (vista : Executable.Vista) (weights : Array Nat) (round : Nat) : Nat → Nat → Bool
  | _,0=>true
  | start,count+1=>selectedCheck vista weights round start && rangeCheck vista weights round (start+1) count

abbrev levelLoop : Routine 48 := forEach 46 balanceItem

def loopSaved (saved : Fin 8 → List Bool) (start count : Nat) : Fin 8 → List Bool :=
  Function.update (Function.update saved 1 (List.replicate (start+count) true)) 4 []

def levelBudget (vista : Executable.Vista) (weights : Array Nat) (round count : Nat) : Nat :=
  count*(100020100*((Encoding.vista.encode vista).length+
    ((Encoding.array Encoding.natural).encode weights).length+round.size+(round+1).size+vista.nodes.size+2)^15+2)+1

/-- Visit exactly the supplied bounded index interval. The status accumulates
only checks at the requested level; both complete input words remain unchanged. -/
theorem levelLoop_executes (vista : Executable.Vista) (weights : Array Nat)
    (valid : vista.valid=true) (length : weights.size=vista.nodes.size)
    (round start count : Nat) (inside : start+count ≤ vista.nodes.size)
    (accepted : Bool) (tail : List Bool) (saved : Fin 8 → List Bool)
    (table : saved 0=Encoding.sequence Encoding.node vista.nodes.toList++Encoding.natural.encode vista.bottom)
    (indexCounter : saved 1=List.replicate start true) (query : saved 2=round.bits) (flag : saved 3=[])
    (counter : saved 4=List.replicate count true) :
    ∃ time ≤ levelBudget vista weights round count,
      Executes levelLoop
        (bankFile (Encoding.vista.encode vista) ((Encoding.array Encoding.natural).encode weights)
          (round+1).bits [] (accepted::tail) saved) time
        (bankFile (Encoding.vista.encode vista) ((Encoding.array Encoding.natural).encode weights)
          (round+1).bits [] ((accepted && rangeCheck vista weights round start count)::tail)
          (loopSaved saved start count)) := by
  induction count generalizing start accepted saved with
  | zero =>
    let store := bankFile (Encoding.vista.encode vista) ((Encoding.array Encoding.natural).encode weights)
      (round+1).bits [] (accepted::tail) saved
    have empty : store 46=[] := by simp [store,bankFile,counter]
    obtain ⟨ran,halted⟩ := repeat_empty (46:Fin 50) balanceItem store empty
    have restored : loopSaved saved start 0=saved := by
      funext i
      by_cases one : i=1 <;> by_cases four : i=4 <;> simp [loopSaved,one,four,indexCounter,counter]
    refine ⟨1,by simp [levelBudget],⟨1,store⟩,ran,halted,?_⟩
    simp only [rangeCheck,Bool.and_true,restored]
    rfl
  | succ count ih =>
    let store := bankFile (Encoding.vista.encode vista) ((Encoding.array Encoding.natural).encode weights)
      (round+1).bits [] (accepted::tail) saved
    let consumedSaved := Function.update saved 4 (List.replicate count true)
    have popped : Function.update store 46 (List.replicate count true)=
        bankFile (Encoding.vista.encode vista) ((Encoding.array Encoding.natural).encode weights)
          (round+1).bits [] (accepted::tail) consumedSaved :=
      bankFile_saved_update _ _ _ _ _ saved 4 _
    obtain ⟨bodyTime,bodyBound,finishBody,bodyRun,bodyHalt,bodyStore⟩ :=
      balanceItem_executes vista weights valid length round start (by omega) accepted tail consumedSaved
        (by simp [consumedSaved,table]) (by simp [consumedSaved,indexCounter])
        (by simp [consumedSaved,query]) (by simp [consumedSaved,flag])
    let nextSaved := Function.update consumedSaved 1 (List.replicate (start+1) true)
    obtain ⟨tailTime,tailBound,finishTail,tailRun,tailHalt,tailStore⟩ :=
      ih (start+1) (by omega) (accepted && selectedCheck vista weights round start) nextSaved
        (by simp [nextSaved,consumedSaved,table]) (by simp [nextSaved])
        (by simp [nextSaved,consumedSaved,query]) (by simp [nextSaved,consumedSaved,flag])
        (by simp [nextSaved,consumedSaved])
    have firstRun := repeat_iteration (46:Fin 50) balanceItem store true (List.replicate count true)
      (by simp [store,bankFile,counter,List.replicate_succ]) bodyTime finishBody
      (by rw [popped];exact bodyRun) bodyHalt
    have finalSaved : loopSaved nextSaved (start+1) count=loopSaved saved start (count+1) := by
      funext i
      by_cases one : i=1 <;> by_cases four : i=4 <;>
        simp [loopSaved,nextSaved,consumedSaved,one,four,Nat.add_comm,Nat.add_left_comm]
    have finalStore :
        bankFile (Encoding.vista.encode vista) ((Encoding.array Encoding.natural).encode weights)
          (round+1).bits []
          (((accepted && selectedCheck vista weights round start) && rangeCheck vista weights round (start+1) count)::tail)
          (loopSaved nextSaved (start+1) count)=
        bankFile (Encoding.vista.encode vista) ((Encoding.array Encoding.natural).encode weights)
          (round+1).bits [] ((accepted && rangeCheck vista weights round start (count+1))::tail)
          (loopSaved saved start (count+1)) := by
      rw [finalSaved]
      simp only [rangeCheck,Bool.and_assoc]
    refine ⟨bodyTime+2+tailTime,?_,finishTail,?_,tailHalt,tailStore.trans finalStore⟩
    · have bodyLimit := bodyBound.trans (Nat.mul_le_mul_left 100020100
        (Nat.pow_le_pow_left (by omega :
          (Encoding.vista.encode vista).length+((Encoding.array Encoding.natural).encode weights).length+
            round.size+(round+1).size+start+2 ≤
          (Encoding.vista.encode vista).length+((Encoding.array Encoding.natural).encode weights).length+
            round.size+(round+1).size+vista.nodes.size+2) 15))
      dsimp only [levelBudget] at tailBound ⊢
      simp only [Nat.add_mul,Nat.one_mul]
      omega
    · rw [Machine.run_add,firstRun,Option.bind_some,bodyStore]
      exact tailRun

end Counting.StackMachine.AuditBalance
