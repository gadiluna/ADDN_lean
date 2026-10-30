import Counting.StackFrameReadPreserving
import Counting.EncodingNetwork

namespace Counting.StackMachine.NetworkVista
open Routine
set_option backward.isDefEq.respectTransparency false

def arcReaderRoles : Fin 8 ↪ Fin 16 := ⟨![1,7,5,6,8,9,10,11],by decide⟩

/-- Read one binary arc multiplicity from a canonical explicit row. Both
the row and the unary receiver index remain available to the simulator. -/
def readArc : Routine 14 := sequence (ofProgram (ListPrograms.copyProgram 13 2 7 12))
  (sequence (pushBit 7 true)
    (sequence (FieldAccess.preservingRead 8 arcReaderRoles)
      (sequence (clear 7) (clear 6))))

theorem readArc_executes (store:Store 14) (row:Array Nat) (index:Fin row.size)
    (source:store 1=(Encoding.array Encoding.natural).encode row)
    (position:(store 2).length=index.val)
    (empty:∀r:Fin 16,r∈({5,6,7,8,9,10,11,12}:Finset (Fin 16)) → store r=[]) :
    ∃time ≤ 10*(store 1).length+14*(store 2).length+40,
      Executes readArc store time (Function.update store 5 row[index.val].bits) := by
  have copying:=copy_executes 13 (2:Fin 16) 7 12 (by decide) (by decide) (by decide) store (empty 12 (by decide))
  rw [empty 7 (by decide),List.append_nil] at copying
  let copied:=Function.update store 7 (store 2)
  have pushing:=pushBit_executes (7:Fin 16) true copied
  let indexed:=Function.update copied 7 (true::store 2)
  have pushed:Function.update copied 7 (true::copied 7)=indexed:=by simp [indexed,copied]
  rw [pushed] at pushing
  obtain ⟨readTime,readBound,reading⟩:=FieldAccess.preservingRead_executes 8 arcReaderRoles indexed
    (by simp [arcReaderRoles,indexed,copied,empty 8 (by decide)])
    (by simp [arcReaderRoles,indexed,copied,empty 9 (by decide)])
    (by simp [arcReaderRoles,indexed,copied,empty 10 (by decide)])
    (by simp [arcReaderRoles,indexed,copied,empty 11 (by decide)])
  have selected:FieldAccess.selectPayload (indexed (arcReaderRoles 0))
      (indexed (arcReaderRoles 1)).length=some row[index.val].bits:=by
    change FieldAccess.selectPayload (indexed 1) (indexed 7).length=_
    rw [show indexed 1=store 1 by simp [indexed,copied],
      show indexed 7=true::store 2 by simp [indexed],List.length_cons,position,source]
    change FieldAccess.selectPayload ((Encoding.list Encoding.natural).encode row.toList) (index.val+1)=_
    rw [FieldAccess.selectPayload_naturalList]
    simp [index.isLt]
  rw [selected,Option.getD_some,Option.isSome_some,
    show indexed (arcReaderRoles 2)=[] by simp [arcReaderRoles,indexed,copied,empty 5 (by decide)],
    show indexed (arcReaderRoles 3)=[] by simp [arcReaderRoles,indexed,copied,empty 6 (by decide)],List.append_nil] at reading
  let readStore:=Function.update (Function.update indexed 5 row[index.val].bits) 6 [true]
  have reading':Executes (FieldAccess.preservingRead 8 arcReaderRoles) indexed readTime readStore:=reading
  have clearIndex:=clear_executes (7:Fin 16) readStore
  rw [show readStore 7=true::store 2 by simp [readStore,indexed]] at clearIndex
  have clearFlag:=clear_executes (6:Fin 16) (Function.update readStore 7 [])
  rw [show Function.update readStore 7 [] 6=[true] by simp [readStore]] at clearFlag
  have final:Function.update (Function.update readStore 7 []) 6 []=Function.update store 5 row[index.val].bits:=by
    funext r
    by_cases n5:r=5 <;> by_cases n6:r=6 <;> by_cases n7:r=7 <;>
      simp [readStore,indexed,copied,n5,n6,n7,empty 6 (by decide),empty 7 (by decide)]
  rw [final] at clearFlag
  have rowSame:indexed (arcReaderRoles 0)=store 1:=by simp [arcReaderRoles,indexed,copied]
  have indexSame:indexed (arcReaderRoles 1)=true::store 2:=by simp [arcReaderRoles,indexed]
  rw [rowSame,indexSame,List.length_cons] at readBound
  refine ⟨_,?_,copying.sequence (pushing.sequence (reading'.sequence (clearIndex.sequence clearFlag)))⟩
  simp only [List.length_cons,List.length_nil]
  omega

end Counting.StackMachine.NetworkVista
