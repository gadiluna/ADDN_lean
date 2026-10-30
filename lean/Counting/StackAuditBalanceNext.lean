import Counting.StackAuditBalanceItem
import Counting.StackDagIncrement

namespace Counting.StackMachine.AuditBalance
open Routine RealizabilityCheck
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

abbrev prepareLevel : Routine 48 := ofProgram (ListPrograms.copyProgram 47 49 46 47)

theorem prepareLevel_executes (source weights target status : List Bool) (saved : Fin 8 → List Bool)
    (count : Nat) (nodeCount : saved 7=List.replicate count true) (e4 : saved 4=[]) (e5 : saved 5=[]) :
    Executes prepareLevel (bankFile source weights target [] status saved) (5*count+2)
      (bankFile source weights target [] status (Function.update saved 4 (List.replicate count true))) := by
  let store := bankFile source weights target [] status saved
  have a := copy_executes 47 (49:Fin 50) 46 47 (by decide) (by decide) (by decide) store
    (by simp [store,bankFile,e5])
  have sourceAt : store 49=List.replicate count true := by simp [store,bankFile,nodeCount]
  have targetAt : store 46=[] := by simp [store,bankFile,e4]
  rw [sourceAt,targetAt,List.append_nil,List.length_replicate] at a
  have result : Function.update store 46 (List.replicate count true)=
      bankFile source weights target [] status (Function.update saved 4 (List.replicate count true)) :=
    bankFile_saved_update _ _ _ _ _ saved 4 _
  rw [result] at a
  exact a

abbrev finishLevel : Routine 48 := sequence (clear 43)
  (sequence (DagValidation.incrementRoutine 47 4 44 47) (DagValidation.incrementRoutine 47 4 22 47))

/-- Erase the completed traversal index and increment both binary level
registers. The preserved unary node budget is never rebuilt from a label. -/
theorem finishLevel_executes (source weights status : List Bool) (saved : Fin 8 → List Bool)
    (round count : Nat) (index : saved 1=List.replicate count true) (level : saved 2=round.bits)
    (scratch : saved 5=[]) :
    ∃ time ≤ count+4*round.size+4*(round+1).size+17,
      Executes finishLevel (bankFile source weights (round+1).bits [] status saved) time
        (bankFile source weights (round+2).bits [] status
          (Function.update (Function.update saved 1 []) 2 (round+1).bits)) := by
  let store := bankFile source weights (round+1).bits [] status saved
  have a := clear_executes (43:Fin 50) store
  have sourceAt : store 43=List.replicate count true := by simp [store,bankFile,index]
  rw [sourceAt,List.length_replicate] at a
  let cleared := Function.update store 43 []
  obtain ⟨firstTime,firstBound,b⟩ := DagValidation.increment_natural 47 (4:Fin 50) 44 47
    (by decide) (by decide) (by decide) cleared
    (by simp [cleared,store,bankFile,massFile])
    (by simp [cleared,store,bankFile,scratch]) round
    (by simp [cleared,store,bankFile,level])
  let raised := Function.update cleared 44 (round+1).bits
  obtain ⟨secondTime,secondBound,c⟩ := DagValidation.increment_natural 47 (4:Fin 50) 22 47
    (by decide) (by decide) (by decide) raised
    (by simp [raised,cleared,store,bankFile,massFile])
    (by simp [raised,cleared,store,bankFile,scratch]) (round+1)
    (by simp [raised,cleared,store,bankFile,massFile])
  have result : Function.update raised 22 (round+1+1).bits=
      bankFile source weights (round+2).bits [] status
        (Function.update (Function.update saved 1 []) 2 (round+1).bits) := by
    funext r
    fin_cases r <;> simp [raised,cleared,store,bankFile,massFile,Nat.add_assoc]
  rw [result] at c
  exact ⟨_,by omega,a.sequence (b.sequence c)⟩

end Counting.StackMachine.AuditBalance
