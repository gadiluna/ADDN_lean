import Counting.StackDagParentRemap
import Counting.StackDagNodeLabels
import Counting.StackEncodingRelabel
import Counting.EncodingNetwork

namespace Counting.StackMachine.DagUpdate.NodeMap
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

def parentRoles : Fin 20 ↪ Fin 64 :=
  ⟨![1,41,45,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20],by decide⟩

def buildParent : Routine 62 := mapRegisters parentRoles remapParent

theorem buildParent_executes (store : Store 62) (mapping : Array Nat) (node : Executable.Node)
    (source : store 1=(Encoding.array Encoding.natural).encode mapping)
    (query : store 41=(parentNumber node).bits)
    (empty : ∀ r : Fin 64,r=45 ∨ (4 ≤ r.val ∧ r.val ≤ 20) → store r=[]) :
    ∃ time ≤ 2100*((store 1).length+(parentNumber node).size+1)^3,
      Executes buildParent store time
        (Function.update store 45 (parentNumber (Executable.referenceMap mapping node)).bits) := by
  let localStore : Store 18:=store ∘ parentRoles
  have localEmpty (r : Fin 20) (n0 : r≠0) (n1 : r≠1) : localStore r=[] := by
    fin_cases r <;> simp_all [localStore,parentRoles]
  obtain ⟨time,bound,ran⟩:=remapParent_executes localStore mapping.toList (parentNumber node)
    (by simpa [localStore,parentRoles,Encoding.array,Encoding.transport] using source)
    query localEmpty
  have resultCode : remapParentCode mapping.toList (parentNumber node)=parentNumber (Executable.referenceMap mapping node) :=
    remapParentCode_referenceMap mapping node
  rw [resultCode] at ran
  refine ⟨time,bound,?_⟩
  apply relocate_executes_frame remapParent parentRoles store
    (Function.update store 45 (parentNumber (Executable.referenceMap mapping node)).bits)
    localStore (Function.update localStore 2 (parentNumber (Executable.referenceMap mapping node)).bits)
    time rfl _ _ ran
  · intro r
    fin_cases r <;> simp [parentRoles,localStore]
  · intro r outside
    have different : r≠45 := fun eq=>outside 2 (by simpa [parentRoles] using eq.symm)
    simp [different]

end Counting.StackMachine.DagUpdate.NodeMap
