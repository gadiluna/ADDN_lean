import Counting.StackDagReadForward
import Counting.StackDagMapInternBank

namespace Counting.StackMachine.DagUpdate.Import
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

def nodeReaderRoles : Fin 20 ↪ Fin 96 :=
  ⟨![70,71,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,0,69,74],by decide⟩

def readImportNode : Routine 94 := mapRegisters nodeReaderRoles readForward

theorem readImportNode_executes (store : Store 94) (node : Executable.Node) (suffix : List Bool)
    (source : store 70=Encoding.node.encode node++suffix) (status : store 71=[true])
    (outputEmpty : store 0=[])
    (empty : ∀ r : Fin 96,2 ≤ r.val → r.val ≤ 16 → store r=[]) :
    ∃ time ≤ 2100*((store 70).length+1)^3,
      Executes readImportNode store time
        (Function.update (Function.update store 70 suffix) 0 (Encoding.node.encode node)) := by
  let localStore : Store 18 := store ∘ nodeReaderRoles
  obtain ⟨time,bound,ran⟩ := readForward_executes localStore node suffix true [] source status (by
    intro r lower upper
    fin_cases r <;> simp_all [localStore,nodeReaderRoles])
  refine ⟨time,bound,?_⟩
  apply relocate_executes_frame readForward nodeReaderRoles store
    (Function.update (Function.update store 70 suffix) 0 (Encoding.node.encode node)) localStore
    (Function.update (Function.update localStore 0 suffix) 17 (Encoding.node.encode node)) time rfl _ _ ran
  · intro r
    fin_cases r <;> simp [localStore,nodeReaderRoles]
  · intro r outside
    have n70 : r≠70 := fun eq=>outside 0 (by simpa [nodeReaderRoles] using eq.symm)
    have n0 : r≠0 := fun eq=>outside 17 (by simpa [nodeReaderRoles] using eq.symm)
    simp [n70,n0]

end Counting.StackMachine.DagUpdate.Import
