import Counting.StackRealizabilityCallFile
import Counting.StackDagDistinctGuard

namespace Counting.StackMachine.VistaComplement
open Routine RealizabilityCall
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

def orderRoles : Fin 6 ↪ Fin 130 := ⟨![103,106,104,0,1,2],by decide⟩
def ordersDifferent : Routine 128 := DagValidation.distinctGuard 124 orderRoles

theorem ordersDifferent_executes (data : Fin 30→List Bool) (accepted : Bool) (tail : List Bool)
    (status : data 4=accepted::tail) :
    ∃ time ≤ 6*((data 3).length+(data 6).length)+18,
      Executes ordersDifferent (file data) time
        (file (Function.update data 4 ((accepted && !decide (data 3=data 6))::tail))) := by
  have run := DagValidation.distinctGuard_executes 124 orderRoles (file data) accepted tail
    (by simpa [orderRoles,file] using status) (by simp [orderRoles,file])
    (by simp [orderRoles,file]) (by simp [orderRoles,file])
  have cost := Compare.preservingCost_le (data 3) (data 6)
  have a : file data (orderRoles 0)=data 3 := by simp [orderRoles,file]
  have b : file data (orderRoles 1)=data 6 := by simp [orderRoles,file]
  rw [a,b] at run
  change Executes ordersDifferent (file data) (Compare.preservingCost (data 3) (data 6)+7)
    (Function.update (file data) (context 4) ((accepted && !decide (data 3=data 6))::tail)) at run
  rw [file_update] at run
  exact ⟨_,by omega,run⟩

theorem canonical_orders_different (first second : Nat) :
    (!decide (Encoding.natural.encode first=Encoding.natural.encode second))=(first != second) := by
  by_cases same : first=second
  · subst second; simp
  · have different := Encoding.natural.injective.ne same
    simp [same,different]

end Counting.StackMachine.VistaComplement
