import Counting.StackDagNodeMapBounds
import Counting.StackDagIntern

namespace Counting.StackMachine.DagUpdate.Import
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

def lowRoles : Fin 64 ↪ Fin 96 := ⟨fun r=>⟨r.val,by have:=r.isLt;omega⟩,by
  intro a b equal
  apply Fin.ext
  exact congrArg (fun r : Fin 96=>r.val) equal⟩

def mapNode : Routine 94 := mapRegisters lowRoles NodeMap.referenceMap
def internNode : Routine 94 := mapRegisters lowRoles Intern.internNode

theorem mapNode_executes (store : Store 94) (mapping : Array Nat) (node : Executable.Node)
    (suffix : List Bool)
    (source : store 0=Encoding.node.encode node++suffix)
    (mappingAt : store 1=(Encoding.array Encoding.natural).encode mapping)
    (empty : ∀ r : Fin 96,2 ≤ r.val → r.val ≤ 48 → store r=[]) :
    ∃ time ≤ 30000000000*((store 0).length+(store 1).length+1)^7,
      Executes mapNode store time
        (Function.update (Function.update store 0 suffix) 3
          (Encoding.node.encode (Executable.referenceMap mapping node))) := by
  let localStore : Store 62 := store ∘ lowRoles
  obtain ⟨time,bound,ran⟩ := NodeMap.referenceMap_executes_polynomial localStore mapping node suffix
    source mappingAt (fun r lower upper=>empty (lowRoles r) lower upper)
  refine ⟨time,bound,?_⟩
  apply relocate_executes_frame NodeMap.referenceMap lowRoles store
    (Function.update (Function.update store 0 suffix) 3
      (Encoding.node.encode (Executable.referenceMap mapping node))) localStore
    (Function.update (Function.update localStore 0 suffix) 3
      (Encoding.node.encode (Executable.referenceMap mapping node))) time rfl _ _ ran
  · intro r
    fin_cases r <;> simp [localStore,lowRoles]
  · intro r outside
    have n0 : r≠0 := fun eq=>outside 0 (by simpa [lowRoles] using eq.symm)
    have n3 : r≠3 := fun eq=>outside 3 (by simpa [lowRoles] using eq.symm)
    simp [n0,n3]

theorem internNode_executes (store : Store 94) (pool : Array Executable.Node) (node : Executable.Node)
    (source : store 0=(Encoding.array Encoding.node).encode pool)
    (nodeAt : store 1=Encoding.node.encode node)
    (empty : ∀ r : Fin 96,2 ≤ r.val → r.val ≤ 37 → store r=[]) :
    ∃ time ≤ 8000*((store 0).length+(store 1).length+1)^4,
      Executes internNode store time
        (Function.update (Function.update store 2 ((Encoding.array Encoding.node).encode (Executable.intern pool node).1))
          3 (Executable.intern pool node).2.bits) := by
  let localStore : Store 62 := store ∘ lowRoles
  obtain ⟨time,bound,ran⟩ := Intern.internNode_executes_array localStore pool node source nodeAt
    (fun r lower upper=>empty (lowRoles r) lower upper)
  refine ⟨time,bound,?_⟩
  apply relocate_executes_frame Intern.internNode lowRoles store
    (Function.update (Function.update store 2 ((Encoding.array Encoding.node).encode (Executable.intern pool node).1))
      3 (Executable.intern pool node).2.bits) localStore
    (Function.update (Function.update localStore 2 ((Encoding.array Encoding.node).encode (Executable.intern pool node).1))
      3 (Executable.intern pool node).2.bits) time rfl _ _ ran
  · intro r
    fin_cases r <;> simp [localStore,lowRoles]
  · intro r outside
    have n2 : r≠2 := fun eq=>outside 2 (by simpa [lowRoles] using eq.symm)
    have n3 : r≠3 := fun eq=>outside 3 (by simpa [lowRoles] using eq.symm)
    simp [n2,n3]

end Counting.StackMachine.DagUpdate.Import
