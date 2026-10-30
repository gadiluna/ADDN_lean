import Counting.StackDagSortRecord
import Counting.StackDagComparePreserving

namespace Counting.StackMachine.DagUpdate.Sort
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

def recordRoles : Fin 20 ↪ Fin 96 := ⟨![80,81,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,65,78,79],by decide⟩

def readSortedRecord : Routine 94 := relocate readRecord recordRoles

def comparisonRoles : Fin 72 ↪ Fin 96 :=
  ⟨fun r=>⟨r.val,by omega⟩,by intro a b equal;exact Fin.ext (congrArg (fun r : Fin 96=>r.val) equal)⟩

def compareSortedNodes : Routine 94 := relocate Key.preservingNodes comparisonRoles

theorem readSortedRecord_executes (store : Store 94) (record : Record) (suffix : List Bool)
    (source : store 80=recordCodec.encode record++suffix) (status : store 81=[true])
    (outputEmpty : store 65=[]) (empty : ∀ r : Fin 96,r.val≤14 → store r=[]) :
    ∃ time≤2100*((store 80).length+1)^3,
      Executes readSortedRecord store time
        (Function.update (Function.update store 80 suffix) 65 (recordCodec.encode record)) := by
  let localStore : Store 18 := store ∘ recordRoles
  obtain ⟨time,bounded,run⟩ := readRecord_executes localStore record suffix true [] source status (by
    intro r lower upper
    fin_cases r <;> simp_all [localStore,recordRoles])
  refine ⟨time,bounded,?_⟩
  apply relocate_executes_frame readRecord recordRoles store _ localStore
    (Function.update (Function.update localStore 0 suffix) 17 (recordCodec.encode record)) time rfl _ _ run
  · intro r
    fin_cases r <;> simp [recordRoles,localStore]
  · intro r outside
    have n80 : r≠80 := fun same=>outside 0 (by simpa [recordRoles] using same.symm)
    have n65 : r≠65 := fun same=>outside 17 (by simpa [recordRoles] using same.symm)
    simp [n80,n65]

theorem compareSortedNodes_executes (store : Store 94) (left right : Executable.Node)
    (leftAt : store 64=Encoding.node.encode left) (rightAt : store 65=Encoding.node.encode right)
    (empty : ∀ r : Fin 96,r.val≤13 ∨ (40≤r.val ∧ r.val≤44) ∨
      (49≤r.val ∧ r.val≤51) ∨ r=67 → store r=[]) :
    ∃ time≤11000*((store 64).length+(store 65).length+1)^2,
      Executes compareSortedNodes store time
        (Function.update store 66 (Executable.lexLE left.key right.key::store 66)) := by
  let localStore : Store 70 := store ∘ comparisonRoles
  obtain ⟨time,bounded,run⟩ := Key.preservingNodes_executes localStore left right leftAt rightAt (by
    intro r allowed
    apply empty (comparisonRoles r)
    simpa [comparisonRoles,Fin.ext_iff] using allowed)
  refine ⟨time,bounded,?_⟩
  apply relocate_executes_frame Key.preservingNodes comparisonRoles store _ localStore
    (Function.update localStore 66 (Executable.lexLE left.key right.key::localStore 66)) time rfl _ _ run
  · intro r
    fin_cases r <;> simp [comparisonRoles,localStore]
  · intro r outside
    have n66 : r≠66 := fun same=>outside 66 (by simpa [comparisonRoles] using same.symm)
    simp [n66]

end Counting.StackMachine.DagUpdate.Sort
