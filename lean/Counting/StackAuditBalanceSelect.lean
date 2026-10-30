import Counting.StackAuditBalanceBank

namespace Counting.StackMachine.AuditBalance
open Routine RealizabilityCheck
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

def selectRoles : Fin 32 ↪ Fin 50 :=
  ⟨![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,42,43,19,20,21,22,23,24,25,26,27,28,29,44,45],by decide⟩

abbrev selectCurrent : Routine 48 := relocate AuditPropagation.selectedLevel selectRoles

/-- Select actual level membership without disturbing the saved DAG,
binary round, unary node index, mass workspace, or audit status. -/
theorem selectCurrent_executes (vista : Executable.Vista) (weights : Array Nat)
    (round index : Nat) (inside : index<vista.nodes.size)
    (accepted : Bool) (tail : List Bool) (saved : Fin 8 → List Bool)
    (table : saved 0=Encoding.sequence Encoding.node vista.nodes.toList++Encoding.natural.encode vista.bottom)
    (counter : saved 1=List.replicate index true) (query : saved 2=round.bits) (flag : saved 3=[]) :
    ∃ time ≤ 8000*((saved 0).length+round.size+1)^4,
      Executes selectCurrent
        (bankFile (Encoding.vista.encode vista) ((Encoding.array Encoding.natural).encode weights)
          (round+1).bits [] (accepted::tail) saved) time
        (Function.update
          (bankFile (Encoding.vista.encode vista) ((Encoding.array Encoding.natural).encode weights)
            (round+1).bits [] (accepted::tail) saved) 45 [decide ((vista.node index).level=round)]) := by
  let store := bankFile (Encoding.vista.encode vista) ((Encoding.array Encoding.natural).encode weights)
    (round+1).bits [] (accepted::tail) saved
  let localStore : Store 30 := store ∘ selectRoles
  have work (r : Fin 32) (small : r.val<17) (different : r≠1) : localStore r=[] := by
    fin_cases r <;> simp_all [localStore,store,bankFile,massFile,selectRoles]
  let index' : Fin vista.nodes.toList.length := ⟨index,by simpa using inside⟩
  obtain ⟨time,bounded,executed⟩ := AuditPropagation.selectedLevel_executes localStore accepted tail
    (by simp [localStore,store,bankFile,massFile,selectRoles]) work
    (by simp [localStore,store,bankFile,massFile,selectRoles]) vista.nodes.toList index'
    (Encoding.natural.encode vista.bottom)
    (by simpa [localStore,store,bankFile,selectRoles] using table)
    (by simp [localStore,store,bankFile,selectRoles,counter,index']) round
    (by simpa [localStore,store,bankFile,selectRoles] using query)
  have selected : vista.nodes.toList[index']=vista.node index := by
    simp [index',Executable.Vista.node,inside]
  have vacant : localStore 31=[] := by simp [localStore,store,bankFile,selectRoles,flag]
  rw [selected,vacant] at executed
  refine ⟨time,by simpa [localStore,store,bankFile,selectRoles] using bounded,?_⟩
  apply relocate_executes_frame AuditPropagation.selectedLevel selectRoles store _ localStore _ time rfl _ _ executed
  · intro r
    fin_cases r <;> simp [localStore,selectRoles,store]
  · intro r outside
    have different : r≠45 := by intro equal;subst r;exact outside 31 rfl
    simp [different,store]

end Counting.StackMachine.AuditBalance
