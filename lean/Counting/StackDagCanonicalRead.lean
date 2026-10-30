import Counting.StackDagCanonicalCommit
import Counting.StackDagSortRecord
import Counting.StackEncodingBoundedNatural

namespace Counting.StackMachine.DagUpdate.Canonical
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

def canonicalReaderRoles : Fin 20 ↪ Fin 96 :=
  ⟨![92,81,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,0,69,74],by decide⟩

def readCanonicalRecord : Routine 94 := relocate Sort.readRecord canonicalReaderRoles

theorem readCanonicalRecord_executes (store : Store 94) (record : Sort.Record) (suffix : List Bool)
    (source : store 92=Sort.recordCodec.encode record++suffix) (status : store 81=[true])
    (e0:store 0=[]) (empty:∀r:Fin 96,2≤r.val → r.val≤16 → store r=[]) :
    ∃time≤2100*((store 92).length+1)^3,
      Executes readCanonicalRecord store time
        (Function.update (Function.update store 92 suffix) 0 (Sort.recordCodec.encode record)) := by
  let localStore:Store 18:=store ∘ canonicalReaderRoles
  obtain ⟨time,bound,run⟩:=Sort.readRecord_executes localStore record suffix true [] source status (by
    intro r lower upper
    fin_cases r <;> simp_all [localStore,canonicalReaderRoles])
  refine ⟨time,bound,?_⟩
  apply relocate_executes_frame Sort.readRecord canonicalReaderRoles store _ localStore
    (Function.update (Function.update localStore 0 suffix) 17 (Sort.recordCodec.encode record)) time rfl _ _ run
  · intro r
    fin_cases r <;> simp [localStore,canonicalReaderRoles]
  · intro r outside
    have n92:r≠92:=fun same=>outside 0 (by simpa [canonicalReaderRoles] using same.symm)
    have n0:r≠0:=fun same=>outside 17 (by simpa [canonicalReaderRoles] using same.symm)
    simp [n92,n0]

def slotCountRoles : CountWorkspace 85 := ⟨![73,75,2,3,4,5,76,6,7,8,79],by decide⟩

/-- Convert only an in-range local index. Its explicit bound is the
serialized mapping length, copied physically and consumed by the converter. -/
def prepareSlot : Routine 94 := sequence (ofProgram (unframeProgram 93 0 72 4))
  (sequence (frameRoutine 93 72 73 4)
    (sequence (ofProgram (ListPrograms.copyProgram 93 1 79 4))
      (sequence (boundedCount 85 slotCountRoles)
        (sequence (clear 73) (sequence (clear 76) (pushBit 75 true))))))

theorem prepareSlot_executes (store:Store 94) (mapping:Array Nat) (record:Sort.Record)
    (inside : record.1 < mapping.size)
    (source:store 0=Sort.recordCodec.encode record)
    (mappingAt:store 1=(Encoding.array Encoding.natural).encode mapping)
    (empty:∀r:Fin 96,(2≤r.val ∧ r.val≤8) ∨ r∈({72,73,75,76,79}:Finset (Fin 96)) → store r=[]) :
    ∃time≤100*((store 0).length+(store 1).length+1)^3,
      Executes prepareSlot store time
        (Function.update (Function.update store 0 (Encoding.node.encode record.2))
          75 (List.replicate (record.1+1) true)) := by
  let M:=(Encoding.array Encoding.natural).encode mapping
  let I:=Encoding.natural.encode record.1
  have unframe:=unframe_canonical_executes 93 (0:Fin 96) 72 4 (by decide) (by decide) (by decide)
    store record.1.bits (Encoding.node.encode record.2)
    (by simpa [Sort.recordCodec,Encoding.product,Encoding.natural] using source)
    (empty 4 (by simp))
  rw [empty 72 (by simp),List.append_nil] at unframe
  let split:=Function.update (Function.update store 0 (Encoding.node.encode record.2)) 72 record.1.bits
  have frame:=frame_executes_updates 93 (72:Fin 96) 73 4 (by decide) (by decide) (by decide) split
    (by simp [split,empty])
  have payload:split 72=record.1.bits:=by simp [split]
  have outEmpty:split 73=[]:=by simp [split,empty]
  rw [payload,outEmpty,List.append_nil] at frame
  let framed:=Function.update (Function.update split 72 []) 73 I
  have copying:=copy_executes 93 (1:Fin 96) 79 4 (by decide) (by decide) (by decide) framed
    (by simp [framed,split,empty])
  have mapValue:framed 1=M:=by simp [framed,split,M,mappingAt]
  have budgetEmpty:framed 79=[]:=by simp [framed,split,empty]
  rw [mapValue,budgetEmpty,List.append_nil] at copying
  let ready:=Function.update framed 79 M
  obtain ⟨countTime,countBound,countRun⟩:=boundedNatural_executes 85 slotCountRoles ready record.1
    (by simp [slotCountRoles,ready,framed,I])
    (by simp [slotCountRoles,ready,framed,split,empty]) (by
      intro r member
      fin_cases r <;> simp_all [slotCountRoles,ready,framed,split])
  have encodedBound:mapping.size≤M.length:=
    Encoding.array_size_le_length Encoding.natural mapping (by intro n _;rw [Encoding.natural_length];omega)
  have fits:record.1≤M.length:=by omega
  have budgetAt:ready (slotCountRoles 10)=M:=by simp [slotCountRoles,ready]
  have counted:boundedNaturalResult 85 slotCountRoles ready record.1=
      Function.update (Function.update (Function.update ready 75 (List.replicate record.1 true)) 79 []) 76 [true]:=by
    simp [boundedNaturalResult,slotCountRoles,ready,framed,split,empty,fits]
  rw [counted] at countRun
  let converted:=Function.update (Function.update (Function.update ready 75 (List.replicate record.1 true)) 79 []) 76 [true]
  have clearHeader:=clear_executes (73:Fin 96) converted
  have headerAt:converted 73=I:=by simp [converted,ready,framed]
  rw [headerAt] at clearHeader
  let noHeader:=Function.update converted 73 []
  have clearFlag:=clear_executes (76:Fin 96) noHeader
  have flagAt:noHeader 76=[true]:=by simp [noHeader,converted]
  rw [flagAt,List.length_singleton] at clearFlag
  let cleaned:=Function.update noHeader 76 []
  have increment:=pushBit_executes (75:Fin 96) true cleaned
  have slotAt:cleaned 75=List.replicate record.1 true:=by simp [cleaned,noHeader,converted]
  rw [slotAt,←List.replicate_succ] at increment
  have final:Function.update cleaned 75 (List.replicate (record.1+1) true)=
      Function.update (Function.update store 0 (Encoding.node.encode record.2))
        75 (List.replicate (record.1+1) true):=by
    funext r
    by_cases r0:r=0 <;> by_cases r72:r=72 <;> by_cases r73:r=73 <;>
      by_cases r75:r=75 <;> by_cases r76:r=76 <;> by_cases r79:r=79 <;>
      simp [cleaned,noHeader,converted,ready,framed,split,r0,r72,r73,r75,r76,r79,empty]
  rw [final] at increment
  refine ⟨_,?_,unframe.sequence (frame.sequence (copying.sequence (countRun.sequence
    (clearHeader.sequence (clearFlag.sequence increment)))))⟩
  rw [budgetAt] at countBound
  have indexBound:I.length≤(store 0).length:=by
    rw [source]
    simp only [Sort.recordCodec,Encoding.product,List.length_append,I]
    omega
  have bitsBound:record.1.bits.length≤I.length:=by
    simp only [I,Encoding.natural_length,Encoding.bits_length];omega
  change countTime≤64*(M.length+I.length+1)^3 at countBound
  have mapLength:M.length=(store 1).length:=congrArg List.length mappingAt.symm
  rw [mapLength] at countBound
  have cubic:((store 1).length+I.length+1)^3≤((store 0).length+(store 1).length+1)^3:=by
    apply Nat.pow_le_pow_left;omega
  have cost:=countBound.trans (Nat.mul_le_mul_left 64 cubic)
  have linear:(store 0).length+(store 1).length+1≤((store 0).length+(store 1).length+1)^3:=
    Nat.le_self_pow (by decide) _
  dsimp only [M]
  rw [←mappingAt]
  omega

end Counting.StackMachine.DagUpdate.Canonical
