import Counting.StackDagMapInternBank
import Counting.StackEncodingFrameStore
import Counting.StackRoutineMove

namespace Counting.StackMachine.DagUpdate.Import
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

def mappingAppendRoles : Fin 10 ↪ Fin 96 := ⟨![1,2,72,3,4,5,6,7,8,9],by decide⟩

def commitNode : Routine 94 := sequence (frameRoutine 93 66 2 4)
  (sequence (mapRegisters mappingAppendRoles appendCanonical)
    (sequence (clear 1) (sequence (move 93 3 1 4) (sequence (clear 2)
      (sequence (clear 64) (sequence (move 93 65 64 4) (pushBit 72 true)))))))

def commitBudget (mapping : Array Nat) (oldPool nextPool : Array Executable.Node) (index : Nat) : Nat :=
  appendCanonicalBudget Encoding.natural mapping.toList index+7*index.bits.length+
  ((Encoding.array Encoding.natural).encode mapping).length+
  ((Encoding.array Encoding.node).encode oldPool).length+
  6*((Encoding.array Encoding.natural).encode (mapping.push index)).length+
  6*((Encoding.array Encoding.node).encode nextPool).length+24

def committed (store : Store 94) (mapping : Array Nat) (nextPool : Array Executable.Node)
    (index : Nat) : Store 94 :=
  Function.update (Function.update (Function.update (Function.update (Function.update store
    1 ((Encoding.array Encoding.natural).encode (mapping.push index)))
    64 ((Encoding.array Encoding.node).encode nextPool)) 65 []) 66 [])
    72 (List.replicate (mapping.size+1) true)

/-- Append the returned binary index to the compact mapping and commit
the new pool. Both replaced words are explicitly erased. -/
theorem commitNode_executes (store : Store 94) (mapping : Array Nat)
    (oldPool nextPool : Array Executable.Node) (index : Nat)
    (mappingAt : store 1=(Encoding.array Encoding.natural).encode mapping)
    (poolAt : store 64=(Encoding.array Encoding.node).encode oldPool)
    (nextAt : store 65=(Encoding.array Encoding.node).encode nextPool)
    (indexAt : store 66=index.bits) (counter : store 72=List.replicate mapping.size true)
    (empty : ∀ r : Fin 96,2 ≤ r.val → r.val ≤ 9 → store r=[]) :
    ∃ time ≤ commitBudget mapping oldPool nextPool index,
      Executes commitNode store time (committed store mapping nextPool index) := by
  let mappingCode := (Encoding.array Encoding.natural).encode mapping
  let nextMapping := (Encoding.array Encoding.natural).encode (mapping.push index)
  let oldCode := (Encoding.array Encoding.node).encode oldPool
  let nextCode := (Encoding.array Encoding.node).encode nextPool
  have framing := frame_executes_updates 93 (66:Fin 96) 2 4 (by decide) (by decide) (by decide)
    store (empty 4 (by decide) (by decide))
  rw [indexAt,empty 2 (by decide) (by decide),List.append_nil] at framing
  let framed := Function.update (Function.update store 66 []) 2 (Encoding.natural.encode index)
  let localStore : Store 8 := framed ∘ mappingAppendRoles
  obtain ⟨appendTime,appendBound,appending⟩ := appendCanonical_executes Encoding.natural mapping.toList index localStore
    (by simpa [localStore,framed,mappingAppendRoles,Encoding.array,Encoding.transport] using mappingAt)
    (by rfl)
    (by simpa [localStore,framed,mappingAppendRoles] using counter) (by
      intro r lower
      fin_cases r <;> simp_all [localStore,framed,mappingAppendRoles])
  have nextCodeEq : (Encoding.list Encoding.natural).encode (mapping.toList++[index])=nextMapping := by
    simp [nextMapping,Encoding.array,Encoding.transport]
  rw [nextCodeEq] at appending
  let appended := Function.update framed 3 nextMapping
  have relocated : Executes (mapRegisters mappingAppendRoles appendCanonical) framed appendTime appended := by
    apply relocate_executes_frame appendCanonical mappingAppendRoles framed appended localStore
      (Function.update localStore 3 nextMapping) appendTime rfl _ _ appending
    · intro r
      fin_cases r <;> simp [appended,localStore,mappingAppendRoles]
    · intro r outside
      have different : r≠3 := fun eq=>outside 3 (by simpa [mappingAppendRoles] using eq.symm)
      simp [appended,different]
  have eraseMapping := clear_executes (1:Fin 96) appended
  have oldMapping : appended 1=mappingCode := by simp [appended,framed,mappingAt,mappingCode]
  rw [oldMapping] at eraseMapping
  let noMapping := Function.update appended 1 []
  have moveMapping := move_executes 93 (3:Fin 96) 1 4 (by decide) (by decide) (by decide)
    noMapping (by simp [noMapping,appended,framed,empty])
  have newMapping : noMapping 3=nextMapping := by simp [noMapping,appended]
  have targetEmpty : noMapping 1=[] := by simp [noMapping]
  rw [newMapping,targetEmpty,List.append_nil] at moveMapping
  let mapped := Function.update (Function.update noMapping 1 nextMapping) 3 []
  have eraseIndex := clear_executes (2:Fin 96) mapped
  have framedIndex : mapped 2=Encoding.natural.encode index := by simp [mapped,noMapping,appended,framed]
  rw [framedIndex,Encoding.natural_length,←Encoding.bits_length] at eraseIndex
  let noIndex := Function.update mapped 2 []
  have erasePool := clear_executes (64:Fin 96) noIndex
  have oldPoolCode : noIndex 64=oldCode := by simp [noIndex,mapped,noMapping,appended,framed,poolAt,oldCode]
  rw [oldPoolCode] at erasePool
  let noPool := Function.update noIndex 64 []
  have movePool := move_executes 93 (65:Fin 96) 64 4 (by decide) (by decide) (by decide)
    noPool (by simp [noPool,noIndex,mapped,noMapping,appended,framed,empty])
  have newPoolCode : noPool 65=nextCode := by
    simp [noPool,noIndex,mapped,noMapping,appended,framed,nextAt,nextCode]
  have poolEmpty : noPool 64=[] := by simp [noPool]
  rw [newPoolCode,poolEmpty,List.append_nil] at movePool
  let pooled := Function.update (Function.update noPool 64 nextCode) 65 []
  have increment := pushBit_executes (72:Fin 96) true pooled
  have current : pooled 72=List.replicate mapping.size true := by
    simp [pooled,noPool,noIndex,mapped,noMapping,appended,framed,counter]
  rw [current,←List.replicate_succ] at increment
  have final : Function.update pooled 72 (List.replicate (mapping.size+1) true)=
      committed store mapping nextPool index := by
    funext r
    fin_cases r <;> simp [pooled,noPool,noIndex,mapped,noMapping,appended,framed,committed,
      nextCode,nextMapping,empty]
  rw [final] at increment
  refine ⟨_,?_,framing.sequence (relocated.sequence (eraseMapping.sequence
    (moveMapping.sequence (eraseIndex.sequence (erasePool.sequence (movePool.sequence increment))))))⟩
  dsimp only [commitBudget,mappingCode,nextMapping,oldCode,nextCode]
  omega

end Counting.StackMachine.DagUpdate.Import
