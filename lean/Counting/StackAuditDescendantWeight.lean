import Counting.StackDagReferenceLookup
import Counting.EncodingNetwork

namespace Counting.StackMachine.AuditDescendant
open Routine
set_option backward.isDefEq.respectTransparency false

def weightRoles : DagUpdate.ReferenceWorkspace 26 :=
  ⟨![32,33,31,0,1,2,3,4,5,6,7,8,9,10],by decide⟩

def readWeight : Routine 38 := DagUpdate.referenceLookup 26 weightRoles

/-- Read the exact default-zero weight while preserving its serialized
array and binary query. Large or missing indices are clipped only to a
budget obtained from the actual array's encoded length. -/
theorem readWeight_executes (store : Store 38) (weights : Array Nat) (ancestor : Nat)
    (source : store 32=(Encoding.array Encoding.natural).encode weights)
    (query : store 33=Encoding.natural.encode ancestor) (e31 : store 31=[])
    (empty : ∀ r : Fin 40,r.val ≤ 10 → store r=[]) :
    ∃ time ≤ 200*((store 32).length+(store 33).length+1)^3,
      Executes readWeight store time
        (Function.update store 31 (weights[ancestor]?.getD 0).bits) := by
  obtain ⟨time,bound,run⟩:=DagUpdate.referenceLookup_executes 26 weightRoles store weights.toList ancestor
    (by simpa [weightRoles,Encoding.array,Encoding.transport] using source) (by simp [weightRoles,query]) (by
      intro r n0 n1 n2
      fin_cases r <;> simp_all [weightRoles])
  refine ⟨time,?_,?_⟩
  · simpa [weightRoles] using bound
  · simpa [readWeight,weightRoles,e31] using run

theorem weight_size_le_encoded (weights : Array Nat) (index : Nat) :
    (weights[index]?.getD 0).size ≤ ((Encoding.array Encoding.natural).encode weights).length := by
  by_cases inside : index<weights.size
  · have member : weights[index]∈weights.toList := by simp
    have bound:=Encoding.array_member_length_le Encoding.natural weights weights[index] member
    simp only [Encoding.natural_length] at bound
    simp only [Array.getElem?_eq_getElem inside,Option.getD_some]
    omega
  · simp [Array.getElem?_eq_none (by omega : weights.size ≤ index)]

end Counting.StackMachine.AuditDescendant
