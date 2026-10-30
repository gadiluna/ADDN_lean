import Counting.StackDagAddCountRead
import Counting.StackDagReferenceLookup
import Counting.StackEncodingFrame

namespace Counting.StackMachine.DagUpdate.Reindex
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

def readRoles : AddWorkspace 20 :=
  ⟨![0,1,2,3,6,7,4,5,8,19,10,11,12,13,14,15,16,17,18,9],by decide⟩

def lookupRoles : ReferenceWorkspace 26 :=
  ⟨![1,6,7,10,11,12,13,14,15,16,17,18,19,20],by decide⟩

def readMapped : Routine 38 := sequence (readCurrent 20 readRoles)
  (sequence (frameRoutine 37 4 6 9) (referenceLookup 26 lookupRoles))

def readMappedResult (store : Store 38) (mapping : List Nat) (index count : Nat) (suffix : List Bool) : Store 38 :=
  Function.update (Function.update (Function.update (Function.update store 0 suffix) 5 count.bits)
    6 (Encoding.natural.encode index)) 7 (mapping[index]?.getD 0).bits

/-- Read a source edge and obtain its new binary reference by scanning the
actual mapping word. No numerical reference controls an unbounded loop. -/
theorem readMapped_executes (store : Store 38) (mapping : List Nat) (index count : Nat) (suffix : List Bool)
    (source : store 0=(Encoding.product Encoding.natural Encoding.natural).encode (index,count)++suffix)
    (mapInput : store 1=(Encoding.list Encoding.natural).encode mapping)
    (empty : ∀ r : Fin 40,4 ≤ r.val → r.val ≤ 20 → store r=[]) :
    ∃ time ≤ 10*index.bits.length+5*count.bits.length+
        200*((store 1).length+(Encoding.natural.encode index).length+1)^3+11,
      Executes readMapped store time (readMappedResult store mapping index count suffix) := by
  have reading:=readCurrent_executes 20 readRoles store index count suffix source
    (empty 4 (by decide) (by decide)) (empty 5 (by decide) (by decide)) (empty 9 (by decide) (by decide))
  let read:=Function.update (Function.update (Function.update store 0 suffix) 4 index.bits) 5 count.bits
  change Executes (readCurrent 20 readRoles) store (5*(index.bits.length+count.bits.length)+5) read at reading
  have framing:=frame_executes 37 (4:Fin 40) 6 9 (by decide) (by decide) (by decide) read
    (by simp [read,empty])
  have indexAt : read 4=index.bits := by simp [read]
  rw [indexAt] at framing
  let framed:=Function.update (Function.update (Function.update store 0 suffix) 5 count.bits) 6 (Encoding.natural.encode index)
  have frameResultEq : frameResult 37 (4:Fin 40) 6 9 read=framed := by
    funext r
    by_cases r4 : r=4
    · subst r;simp [frameResult,framed,empty]
    · by_cases r6 : r=6
      · subst r;simp [frameResult,framed,read,empty,Encoding.natural]
      · by_cases r9 : r=9
        · subst r;simp [frameResult,framed,empty]
        · by_cases r0 : r=0 <;> by_cases r5 : r=5 <;>
            simp [frameResult,framed,read,r0,r4,r5,r6,r9]
  rw [frameResultEq] at framing
  have lookupEmpty (j : Fin 14) (n0 : j≠0) (n1 : j≠1) (n2 : j≠2) : framed (lookupRoles j)=[] := by
    fin_cases j <;> simp_all [lookupRoles,framed]
  obtain ⟨lookupTime,lookupBound,lookupRun⟩:=referenceLookup_executes 26 lookupRoles framed mapping index
    (by simp [lookupRoles,framed,mapInput]) (by simp [lookupRoles,framed]) lookupEmpty
  have mapAt : framed (lookupRoles 0)=store 1 := by simp [lookupRoles,framed]
  have queryAt : framed (lookupRoles 1)=Encoding.natural.encode index := by simp [lookupRoles,framed]
  have outputAt : framed (lookupRoles 2)=[] := by simp [lookupRoles,framed,empty]
  rw [mapAt,queryAt] at lookupBound
  rw [outputAt,List.append_nil] at lookupRun
  refine ⟨5*(index.bits.length+count.bits.length)+5+1+(5*index.bits.length+4+1+lookupTime),by omega,?_⟩
  exact reading.sequence (framing.sequence lookupRun)

end Counting.StackMachine.DagUpdate.Reindex
