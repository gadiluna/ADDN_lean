import Counting.StackLexComplete
import Counting.StackRegisterFrames

namespace Counting.StackMachine.DagUpdate.Key
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

def keyComparisonRoles : Fin 16 ↪ Fin 64 := ⟨![4,5,6,2,7,8,9,10,11,12,50,51,49,13,14,15],by decide⟩
def compareKeys : Routine 62 := relocate Lexicographic.compareStreams keyComparisonRoles

theorem compareKeys_executes (store : Store 62) (left right : List Nat)
    (leftAt : store 50=Encoding.sequence Encoding.natural left)
    (rightAt : store 51=Encoding.sequence Encoding.natural right)
    (empty : ∀ r : Fin 64,r=2 ∨ (4≤r.val ∧ r.val≤13) ∨ r=49 → store r=[]) :
    ∃ time≤100*((store 50).length+(store 51).length+1)^2,
      Executes compareKeys store time
        (Function.update (Function.update (Function.update store 50 []) 51 []) 2 [Executable.lexLE left right]) := by
  let localStore : Store 14 := store ∘ keyComparisonRoles
  obtain ⟨time,bounded,run⟩ := Lexicographic.compareStreams_executes localStore left right
    leftAt rightAt (by
      intro r allowed
      fin_cases r <;> simp_all [localStore,keyComparisonRoles])
  refine ⟨time,bounded,?_⟩
  apply relocate_executes_frame Lexicographic.compareStreams keyComparisonRoles store _ localStore
    (Lexicographic.comparisonResult localStore left right) time rfl _ _ run
  · intro r
    fin_cases r <;> simp [keyComparisonRoles,Lexicographic.comparisonResult,localStore]
  · intro r outside
    have n2 : r≠2 := fun same=>outside 3 (by simpa [keyComparisonRoles] using same.symm)
    have n50 : r≠50 := fun same=>outside 10 (by simpa [keyComparisonRoles] using same.symm)
    have n51 : r≠51 := fun same=>outside 11 (by simpa [keyComparisonRoles] using same.symm)
    simp [n2,n50,n51]

end Counting.StackMachine.DagUpdate.Key
