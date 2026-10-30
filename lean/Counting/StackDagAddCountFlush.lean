import Counting.StackDagAddCountSelect

namespace Counting.StackMachine.DagUpdate
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false

def flushPending (extra : Nat) (w : AddWorkspace extra) : Routine (extra+18) :=
  branchRoutine (w 4) (emitNew extra w) (skip (extra+18))

def flushResult (w : AddWorkspace extra) (store : Store (extra+18))
    (index count : Nat) (pending : Bool) (tail : List Bool) : Store (extra+18) :=
  let edges:=if pending then [(index,count)] else []
  Function.update (Function.update (Function.update store (w 4) tail)
    (w 3) ((Encoding.sequence edgeCodec edges).reverse++store (w 3)))
    (w 5) (List.replicate edges.length true++store (w 5))

theorem flushPending_executes (extra : Nat) (w : AddWorkspace extra) (store : Store (extra+18))
    (index count : Nat) (pending : Bool) (tail : List Bool)
    (query : store (w 1)=index.bits) (increment : store (w 2)=count.bits)
    (flag : store (w 4)=pending::tail)
    (empty : ∀ j∈([8,9,10,15,16]:List (Fin 20)),store (w j)=[]) :
    ∃ time ≤ 14*(index.bits.length+count.bits.length)+26,
      Executes (flushPending extra w) store time (flushResult w store index count pending tail) := by
  let consumed:=Function.update store (w 4) tail
  cases pending
  · have skipped:=skip_executes consumed
    have branch:=branch_executes_false (w 4) (emitNew extra w) (skip (extra+18)) store consumed tail 0 flag skipped
    refine ⟨1,by omega,?_⟩
    have same : flushResult w store index count false tail=consumed := by
      funext r
      by_cases a : r=w 3 <;> by_cases b : r=w 5 <;>
        simp [flushResult,consumed,Encoding.sequence,Function.update_apply,a,b,w.injective.eq_iff]
    rw [same]
    simpa only [flushPending,Nat.add_zero] using branch
  · have copiedEmpty (j : Fin 20) (member : j∈([8,9,10,15,16]:List (Fin 20))) : consumed (w j)=[] := by
      have different : j≠4 := by intro eq;subst j;simp at member
      simpa [consumed,w.injective.eq_iff,different] using empty j member
    have emitting:=emitNew_executes extra w consumed copiedEmpty
    have queryAt : consumed (w 1)=index.bits := by simp [consumed,w.injective.eq_iff,query]
    have countAt : consumed (w 2)=count.bits := by simp [consumed,w.injective.eq_iff,increment]
    rw [queryAt,countAt] at emitting
    have branch:=branch_executes_true (w 4) (emitNew extra w) (skip (extra+18)) store _ tail _ flag emitting
    refine ⟨1+(14*(index.bits.length+count.bits.length)+25),by omega,?_⟩
    simpa [flushPending,flushResult,Encoding.sequence,edgeCodec,Encoding.product,Encoding.natural,
      consumed,w.injective.eq_iff] using branch

end Counting.StackMachine.DagUpdate
