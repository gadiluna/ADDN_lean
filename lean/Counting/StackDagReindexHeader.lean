import Counting.StackEncodingListReadHeader
import Counting.StackDagAddCountActions
import Counting.StackRoutineFixedPrefix

namespace Counting.StackMachine.DagUpdate.Reindex
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

def headerRoles : FullListWorkspace 23 :=
  ⟨![0,4,5,6,3,7,1,2,8,9,10,11,12,13,14,15,16],by decide⟩

def readHeader : Routine 38 := sequence (pushBit 4 true)
  (sequence (readListHeader 23 headerRoles) (discardBit 4))

theorem readHeader_executes (store : Store 38) (edges : List (Nat×Nat)) (suffix : List Bool)
    (source : store 0=(Encoding.list edgeCodec).encode edges++suffix)
    (empty : ∀ r : Fin 40,3 ≤ r.val → r.val ≤ 16 → store r=[]) :
    ∃ time ≤ 1820*((store 0).length+1)^3+4,
      Executes readHeader store time
        (Function.update (Function.update store 0 (Encoding.sequence edgeCodec edges++suffix)) 3
          (List.replicate edges.length true)) := by
  have starting:=pushBit_executes (4:Fin 40) true store
  rw [empty 4 (by decide) (by decide)] at starting
  let started:=Function.update store 4 [true]
  obtain ⟨time,bound,reading⟩:=readListHeader_canonical 23 headerRoles started true []
    (by simp [headerRoles,started]) (by
      intro r member
      fin_cases r <;> simp_all [headerRoles,started]) edgeCodec
    (fun edge=>by simp [edgeCodec,Encoding.product,Encoding.natural_length]) edges suffix
    (by simp [headerRoles,started,source])
  let read:=Function.update (Function.update started 0 (Encoding.sequence edgeCodec edges++suffix)) 3
    (List.replicate edges.length true)
  have clearing:=discardBit_executes (4:Fin 40) read
  have flagAt : read 4=[true] := by simp [read,started]
  rw [flagAt,List.tail_cons] at clearing
  have final : Function.update read 4 []=
      Function.update (Function.update store 0 (Encoding.sequence edgeCodec edges++suffix)) 3
        (List.replicate edges.length true) := by
    funext r
    by_cases r4 : r=4
    · subst r;simp [empty]
    · by_cases r0 : r=0 <;> by_cases r3 : r=3 <;> simp [read,started,r0,r3,r4]
  rw [final] at clearing
  have inputAt : started (headerRoles 0)=store 0 := by simp [started,headerRoles]
  rw [inputAt] at bound
  exact ⟨1+1+(time+1+1),by omega,starting.sequence (reading.sequence clearing)⟩

end Counting.StackMachine.DagUpdate.Reindex
