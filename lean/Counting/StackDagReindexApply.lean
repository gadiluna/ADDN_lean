import Counting.StackDagAddCountBounds
import Counting.StackRoutineMove

namespace Counting.StackMachine.DagUpdate.Reindex
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

def addRoles : AddWorkspace 20 :=
  ⟨![2,7,5,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37],by decide⟩

def applyMapped : Routine 38 := sequence (addCount 20 addRoles)
  (sequence (move 37 21 2 9) (sequence (clear 5) (sequence (clear 6) (clear 7))))

def applyMappedResult (store : Store 38) (index count : Nat) (edges : List (Nat×Nat)) : Store 38 :=
  Function.update (Function.update (Function.update (Function.update store 2
    ((Encoding.list edgeCodec).encode (Executable.addCount index count edges))) 5 []) 6 []) 7 []

theorem applyMapped_executes (store : Store 38) (index count : Nat) (edges : List (Nat×Nat))
    (source : store 2=(Encoding.list edgeCodec).encode edges)
    (query : store 7=index.bits) (increment : store 5=count.bits)
    (empty : ∀ r : Fin 40,r=9 ∨ (21 ≤ r.val ∧ r.val ≤ 37) → store r=[]) :
    ∃ time ≤ 10000*((store 2).length+index.bits.length+count.bits.length+1)^3+
        6*((Encoding.list edgeCodec).encode (Executable.addCount index count edges)).length+
        count.bits.length+(store 6).length+index.bits.length+12,
      Executes applyMapped store time (applyMappedResult store index count edges) := by
  have workEmpty (j : Fin 20) (n0 : j≠0) (n1 : j≠1) (n2 : j≠2) : store (addRoles j)=[] := by
    fin_cases j <;> simp_all [addRoles]
  obtain ⟨updateTime,updateBound,updating⟩:=addCount_executes_polynomial 20 addRoles store index count edges []
    (by simpa [addRoles] using source) query increment workEmpty
  let code:=(Encoding.list edgeCodec).encode (Executable.addCount index count edges)
  let updated:=Function.update (Function.update store 2 []) 21 code
  change Executes (addCount 20 addRoles) store updateTime updated at updating
  change updateTime ≤ 10000*((store 2).length+(store 7).length+(store 5).length+1)^3 at updateBound
  rw [query,increment] at updateBound
  have moving:=move_executes 37 (21:Fin 40) 2 9 (by decide) (by decide) (by decide) updated
    (by simp [updated,empty])
  have sourceAt : updated 21=code := by simp [updated]
  have outputAt : updated 2=[] := by simp [updated]
  rw [sourceAt,outputAt,List.append_nil] at moving
  let moved:=Function.update store 2 code
  have movedEq : Function.update (Function.update updated 2 code) 21 []=moved := by
    funext r
    by_cases a : r=2 <;> by_cases b : r=21 <;> simp [updated,moved,a,b,empty]
  rw [movedEq] at moving
  have clearCount:=clear_executes (5:Fin 40) moved
  have countAt : moved 5=count.bits := by simp [moved,increment]
  rw [countAt] at clearCount
  let countCleared:=Function.update moved 5 []
  have clearHeader:=clear_executes (6:Fin 40) countCleared
  have headerAt : countCleared 6=store 6 := by simp [countCleared,moved]
  rw [headerAt] at clearHeader
  let headerCleared:=Function.update countCleared 6 []
  have clearQuery:=clear_executes (7:Fin 40) headerCleared
  have queryAt : headerCleared 7=index.bits := by simp [headerCleared,countCleared,moved,query]
  rw [queryAt] at clearQuery
  refine ⟨_,?_,updating.sequence (moving.sequence (clearCount.sequence (clearHeader.sequence clearQuery)))⟩
  dsimp only [code]
  omega

end Counting.StackMachine.DagUpdate.Reindex
