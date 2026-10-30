import Counting.StackDagMapInternBank
import Counting.StackFramedWrite
import Counting.StackFrameReplaceArray
import Counting.StackDagCanonicalSpec

namespace Counting.StackMachine.DagUpdate.Canonical
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

def mappingWriteRoles : Fin 6 ↪ Fin 96 := ⟨![1,75,3,4,5,6],by decide⟩

/-- Intern an already remapped signature and replace its original mapping
slot. The unary slot includes the list-length header offset. -/
def commitSignature : Routine 94 := sequence (move 93 1 68 4)
  (sequence (move 93 0 1 4)
    (sequence (ofProgram (ListPrograms.copyProgram 93 64 0 4))
      (sequence Import.internNode
        (sequence (clear 0) (sequence (clear 1)
          (sequence (move 93 68 1 4) (sequence (clear 64)
            (sequence (move 93 2 64 4) (FieldAccess.writePayload 90 mappingWriteRoles)))))))))

def commitBudget (state : Executable.CanonicalState) (record : Sort.Record) : Nat :=
  let result:=Executable.intern state.1 record.2
  let P:=((Encoding.array Encoding.node).encode state.1).length
  let Q:=(Encoding.node.encode record.2).length
  let M:=((Encoding.array Encoding.natural).encode state.2).length
  8000*(P+Q+1)^4+17*M+7*Q+7*P+
    6*((Encoding.array Encoding.node).encode result.1).length+3*(record.1+1)+17*result.2.size+100

theorem commitSignature_executes (store : Store 94) (state : Executable.CanonicalState)
    (record : Sort.Record) (inside : record.1<state.2.size)
    (queryAt : store 0=Encoding.node.encode record.2)
    (mappingAt : store 1=(Encoding.array Encoding.natural).encode state.2)
    (poolAt : store 64=(Encoding.array Encoding.node).encode state.1)
    (slotAt : store 75=List.replicate (record.1+1) true)
    (empty : ∀r:Fin 96,(2≤r.val ∧ r.val≤37) ∨ r=68 → store r=[]) :
    ∃time≤commitBudget state record,
      Executes commitSignature store time
        (Function.update (Function.update (Function.update (Function.update store 0 []) 75 [])
          1 ((Encoding.array Encoding.natural).encode (commitRecord state record).2))
          64 ((Encoding.array Encoding.node).encode (commitRecord state record).1)) := by
  let P:=(Encoding.array Encoding.node).encode state.1
  let Q:=Encoding.node.encode record.2
  let M:=(Encoding.array Encoding.natural).encode state.2
  let result:=Executable.intern state.1 record.2
  let R:=(Encoding.array Encoding.node).encode result.1
  have saveMapping:=move_executes 93 (1:Fin 96) 68 4 (by decide) (by decide) (by decide) store
    (empty 4 (by simp))
  rw [mappingAt,empty 68 (by simp),List.append_nil] at saveMapping
  let saved:=Function.update (Function.update store 68 M) 1 []
  have moveQuery:=move_executes 93 (0:Fin 96) 1 4 (by decide) (by decide) (by decide) saved
    (by simp [saved,empty])
  have qAt:saved 0=Q:=by simp [saved,Q,queryAt]
  have qEmpty:saved 1=[]:=by simp [saved]
  rw [qAt,qEmpty,List.append_nil] at moveQuery
  let queried:=Function.update (Function.update saved 1 Q) 0 []
  have copyPool:=copy_executes 93 (64:Fin 96) 0 4 (by decide) (by decide) (by decide) queried
    (by simp [queried,saved,empty])
  have pAt:queried 64=P:=by simp [queried,saved,P,poolAt]
  have pEmpty:queried 0=[]:=by simp [queried]
  rw [pAt,pEmpty,List.append_nil] at copyPool
  let ready:=Function.update queried 0 P
  obtain ⟨internTime,internBound,interning⟩:=Import.internNode_executes ready state.1 record.2
    (by rfl) (by simp [ready,queried,Q]) (by
      intro r lower upper
      have n0:r≠0:=by intro eq;subst r;norm_num at lower
      have n1:r≠1:=by intro eq;subst r;norm_num at lower
      have n68:r≠68:=by intro eq;subst r;norm_num at upper
      simp [ready,queried,saved,n0,n1,n68,empty r (Or.inl ⟨lower,upper⟩)])
  let interned:=Function.update (Function.update ready 2 R) 3 result.2.bits
  have clearPool:=clear_executes (0:Fin 96) interned
  have oldP:interned 0=P:=by simp [interned,ready]
  rw [oldP] at clearPool
  let noPool:=Function.update interned 0 []
  have clearQuery:=clear_executes (1:Fin 96) noPool
  have oldQ:noPool 1=Q:=by simp [noPool,interned,ready,queried]
  rw [oldQ] at clearQuery
  let noQuery:=Function.update noPool 1 []
  have restoreMapping:=move_executes 93 (68:Fin 96) 1 4 (by decide) (by decide) (by decide) noQuery
    (by simp [noQuery,noPool,interned,ready,queried,saved,empty])
  have savedM:noQuery 68=M:=by simp [noQuery,noPool,interned,ready,queried,saved]
  have emptyM:noQuery 1=[]:=by simp [noQuery]
  rw [savedM,emptyM,List.append_nil] at restoreMapping
  let restored:=Function.update (Function.update noQuery 1 M) 68 []
  have clearOriginal:=clear_executes (64:Fin 96) restored
  have original:restored 64=P:=by simp [restored,noQuery,noPool,interned,ready,queried,saved,P,poolAt]
  rw [original] at clearOriginal
  let noOriginal:=Function.update restored 64 []
  have moveResult:=move_executes 93 (2:Fin 96) 64 4 (by decide) (by decide) (by decide) noOriginal
    (by simp [noOriginal,restored,noQuery,noPool,interned,ready,queried,saved,empty])
  have resultAt:noOriginal 2=R:=by simp [noOriginal,restored,noQuery,noPool,interned]
  have resultEmpty:noOriginal 64=[]:=by simp [noOriginal]
  rw [resultAt,resultEmpty,List.append_nil] at moveResult
  let pooled:=Function.update (Function.update noOriginal 64 R) 2 []
  obtain ⟨writeTime,writeBound,writing⟩:=FieldAccess.writePayload_executes 90 mappingWriteRoles pooled
    (by simp [mappingWriteRoles,pooled,noOriginal,restored,noQuery,noPool,interned,ready,queried,saved,empty])
    (by simp [mappingWriteRoles,pooled,noOriginal,restored,noQuery,noPool,interned,ready,queried,saved,empty])
    (by simp [mappingWriteRoles,pooled,noOriginal,restored,noQuery,noPool,interned,ready,queried,saved,empty])
  have mapValue:pooled (mappingWriteRoles 0)=M:=by simp [mappingWriteRoles,pooled,noOriginal,restored]
  have slotValue:pooled (mappingWriteRoles 1)=List.replicate (record.1+1) true:=by
    simp [mappingWriteRoles,pooled,noOriginal,restored,noQuery,noPool,interned,ready,queried,saved,slotAt]
  have indexValue:pooled (mappingWriteRoles 2)=result.2.bits:=by
    simp [mappingWriteRoles,pooled,noOriginal,restored,noQuery,noPool,interned]
  have final:FieldAccess.writePayloadResult mappingWriteRoles pooled=
      Function.update (Function.update (Function.update (Function.update store 0 []) 75 [])
        1 ((Encoding.array Encoding.natural).encode (commitRecord state record).2))
        64 ((Encoding.array Encoding.node).encode (commitRecord state record).1):=by
    unfold FieldAccess.writePayloadResult
    rw [mapValue,slotValue,indexValue,List.length_replicate]
    change Function.update (Function.update (Function.update pooled 75 []) 3 []) 1
      (FieldAccess.replaceFieldWord ((Encoding.array Encoding.natural).encode state.2) (record.1+1)
        (Encoding.natural.encode result.2))=_
    rw [FieldAccess.replaceFieldWord_naturalArray _ _ _ inside]
    funext r
    by_cases r0:r=0 <;> by_cases r1:r=1 <;> by_cases r2:r=2 <;> by_cases r3:r=3 <;>
      by_cases r64:r=64 <;> by_cases r68:r=68 <;> by_cases r75:r=75 <;>
      simp [commitRecord,Array.set!_eq_setIfInBounds,pooled,noOriginal,restored,noQuery,noPool,
        interned,ready,queried,saved,R,result,r0,r1,r2,r3,r64,r68,r75,empty]
  rw [final] at writing
  refine ⟨_,?_,saveMapping.sequence (moveQuery.sequence (copyPool.sequence (interning.sequence
    (clearPool.sequence (clearQuery.sequence (restoreMapping.sequence (clearOriginal.sequence
      (moveResult.sequence writing))))))))⟩
  rw [mapValue,slotValue,indexValue,List.length_replicate,Encoding.bits_length] at writeBound
  have readyP:ready 0=P:=by simp [ready]
  have readyQ:ready 1=Q:=by simp [ready,queried]
  rw [readyP,readyQ] at internBound
  dsimp only [commitBudget]
  dsimp only [P,Q,M,R,result] at *
  omega

end Counting.StackMachine.DagUpdate.Canonical
