import Counting.StackFramedWrite
import Counting.StackFrameReplaceArray
import Counting.StackUnframeCanonical

namespace Counting.StackMachine.AuditPropagation
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false

def assignRoles : Fin 6 ↪ Fin 37 := ⟨![35,31,21,2,3,4],by decide⟩

/-- Consume one anchor coordinate from the real natural stream and replace
its bounded-index field in the real serialized weight array. -/
abbrev assignNode : Routine 35 := sequence (ofProgram (unframeProgram 34 36 21 4))
  (FieldAccess.writePayload 31 assignRoles)

theorem assignNode_executes (store : Store 35) (weights : Array Nat) (index value : Nat)
    (inside : index<weights.size) (suffix : List Bool)
    (source : store 36=Encoding.natural.encode value++suffix)
    (array : store 35=(Encoding.array Encoding.natural).encode weights)
    (counter : store 31=List.replicate (index+1) true)
    (e2 : store 2=[]) (e3 : store 3=[]) (e4 : store 4=[]) (e21 : store 21=[]) :
    ∃ time ≤ 5*(store 35).length+3*(index+1)+22*value.size+24,
      Executes assignNode store time
        (Function.update (Function.update (Function.update store 36 suffix) 31 []) 35
          ((Encoding.array Encoding.natural).encode (weights.setIfInBounds index value))) := by
  have parsed := unframe_canonical_executes 34 (36:Fin 37) 21 4
    (by decide) (by decide) (by decide) store value.bits suffix source e4
  rw [e21,List.append_nil] at parsed
  let ready := Function.update (Function.update store 36 suffix) 21 value.bits
  obtain ⟨time,bounded,ran⟩ := FieldAccess.writePayload_executes 31 assignRoles ready
    (by simp [assignRoles,ready,e2]) (by simp [assignRoles,ready,e3]) (by simp [assignRoles,ready,e4])
  have sourceAt : ready (assignRoles 0)=(Encoding.array Encoding.natural).encode weights := by
    simp [assignRoles,ready,array]
  have counterAt : ready (assignRoles 1)=List.replicate (index+1) true := by
    simp [assignRoles,ready,counter]
  have payloadAt : ready (assignRoles 2)=value.bits := by simp [assignRoles,ready]
  have output : FieldAccess.writePayloadResult assignRoles ready=
      Function.update (Function.update (Function.update store 36 suffix) 31 []) 35
        ((Encoding.array Encoding.natural).encode (weights.setIfInBounds index value)) := by
    unfold FieldAccess.writePayloadResult
    rw [sourceAt,counterAt,payloadAt,List.length_replicate]
    change Function.update (Function.update (Function.update ready 31 []) 21 []) 35
      (FieldAccess.replaceFieldWord ((Encoding.array Encoding.natural).encode weights) (index+1)
        (Encoding.natural.encode value))=_
    rw [FieldAccess.replaceFieldWord_naturalArray weights index value inside]
    funext target
    by_cases a : target=35 <;> by_cases b : target=31 <;> by_cases c : target=21 <;>
      simp [ready,a,b,c,e21]
  rw [output] at ran
  refine ⟨_,?_,parsed.sequence ran⟩
  rw [sourceAt,counterAt,payloadAt,List.length_replicate,Encoding.bits_length,←array] at bounded
  simp only [Encoding.bits_length]
  omega

end Counting.StackMachine.AuditPropagation
