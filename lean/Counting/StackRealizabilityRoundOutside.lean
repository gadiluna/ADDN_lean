import Counting.StackRealizabilityRoundFile

namespace Counting.StackMachine.RealizabilityCheck
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

def roundOutsideRoles : Fin 9 ↪ Fin 100 := ⟨![82,96,87,93,0,2,3,4,5],by decide⟩
def roundOutside : Routine 98 := mapRegisters roundOutsideRoles outsideVector

theorem roundOutside_executes (data : Fin 20→List Bool) (order visible : Nat)
    (hn : data 2=order.bits) (hv : data 16=visible.bits) (empty : data 13=[]) :
    ∃ time ≤ 40*(order.size+visible.size+(data 7).length+1),
      Executes roundOutside (roundFile data) time
        (roundFile (Function.update data 13
          (List.replicate ((data 7).length-1) false++[decide (0<order-visible)]))) := by
  let localStore : Store 7 := roundFile data ∘ roundOutsideRoles
  obtain ⟨time,bound,run⟩ := outsideVector_executes localStore order visible
    (by simp [localStore,roundFile,roundOutsideRoles,hn])
    (by simp [localStore,roundFile,roundOutsideRoles,hv])
    (by simp [localStore,roundFile,roundOutsideRoles])
    (by simp [localStore,roundFile,roundOutsideRoles])
    (by simp [localStore,roundFile,roundOutsideRoles])
    (by simp [localStore,roundFile,roundOutsideRoles])
  refine ⟨time,by simpa [localStore,roundFile,roundOutsideRoles] using bound,?_⟩
  apply relocate_executes_frame outsideVector roundOutsideRoles (roundFile data) _ localStore _ time rfl _ _ run
  · intro r
    fin_cases r <;> simp [localStore,roundFile,roundOutsideRoles,empty]
  · intro r outside
    have different : r≠93 := by intro same;subst r;exact outside 3 rfl
    rw [←roundFile_update]
    exact Function.update_of_ne different _ _

end Counting.StackMachine.RealizabilityCheck
