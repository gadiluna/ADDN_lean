import Counting.StackDagMapInternBank
import Counting.StackEncodingFrame
import Counting.EncodingNetwork

namespace Counting.StackMachine.DagUpdate.Raw
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

def internVista (pool : Array Executable.Node) (node : Executable.Node) : Executable.Vista :=
  let result := Executable.intern pool node
  ⟨result.1,result.2⟩

def finish : Routine 94 := sequence (move 93 64 0 69)
  (sequence Import.internNode (sequence (clear 0) (sequence (clear 1)
    (sequence (frameRoutine 93 3 1 4) (sequence (move 93 2 1 4) (clear 71))))))

def finishBudget (pool : Array Executable.Node) (node : Executable.Node) : Nat :=
  let P := ((Encoding.array Encoding.node).encode pool).length
  let Q := (Encoding.node.encode node).length
  let result := Executable.intern pool node
  8000*(P+Q+1)^4+7*P+Q+5*result.2.bits.length+
    6*((Encoding.array Encoding.node).encode result.1).length+22

def finishedStore (store : Store 94) (pool : Array Executable.Node) (node : Executable.Node) : Store 94 :=
  Function.update (Function.update (Function.update store 64 []) 71 [])
    1 (Encoding.vista.encode (internVista pool node))

theorem finish_executes (store : Store 94) (pool : Array Executable.Node) (node : Executable.Node)
    (poolAt : store 64=(Encoding.array Encoding.node).encode pool)
    (nodeAt : store 1=Encoding.node.encode node) (flag : store 71=[true])
    (empty : ∀ r:Fin 96,r=0 ∨ (2≤r.val ∧ r.val≤37) ∨ r=69 → store r=[]) :
    ∃ time ≤ finishBudget pool node,
      Executes finish store time (finishedStore store pool node) := by
  let P := (Encoding.array Encoding.node).encode pool
  let Q := Encoding.node.encode node
  let result := Executable.intern pool node
  let R := (Encoding.array Encoding.node).encode result.1
  have moving := move_executes 93 (64:Fin 96) 0 69 (by decide) (by decide) (by decide)
    store (empty 69 (by simp))
  rw [poolAt,empty 0 (by simp),List.append_nil] at moving
  let a := Function.update (Function.update store 0 P) 64 []
  obtain ⟨ti,bi,ri⟩ := Import.internNode_executes a pool node
    (by simp [a,P]) (by simp [a,nodeAt]) (by
      intro r lo hi
      have n0:r≠0 := by intro eq;subst r;norm_num at lo
      have n64:r≠64 := by intro eq;subst r;norm_num at hi
      simp [a,n0,n64,empty r (Or.inr (Or.inl ⟨lo,hi⟩))])
  let b := Function.update (Function.update a 2 R) 3 result.2.bits
  have clearP := clear_executes (0:Fin 96) b
  rw [show b 0=P by simp [b,a]] at clearP
  let c := Function.update b 0 []
  have clearQ := clear_executes (1:Fin 96) c
  rw [show c 1=Q by simp [c,b,a,Q,nodeAt]] at clearQ
  let d := Function.update c 1 []
  have framed := frame_executes 93 (3:Fin 96) 1 4 (by decide) (by decide) (by decide)
    d (by simp [d,c,b,a,empty])
  rw [show d 3=result.2.bits by simp [d,c,b]] at framed
  let e := Function.update (Function.update d 3 []) 1 (Encoding.natural.encode result.2)
  have framedEq : frameResult 93 (3:Fin 96) 1 4 d=e := by
    funext r
    by_cases n1:r=1 <;> by_cases n3:r=3 <;> by_cases n4:r=4 <;>
      simp [frameResult,e,d,c,b,a,Encoding.natural,n1,n3,n4,empty]
  rw [framedEq] at framed
  have output := move_executes 93 (2:Fin 96) 1 4 (by decide) (by decide) (by decide)
    e (by simp [e,d,c,b,a,empty])
  rw [show e 2=R by simp [e,d,c,b],show e 1=Encoding.natural.encode result.2 by simp [e]] at output
  let f := Function.update (Function.update e 1 (R++Encoding.natural.encode result.2)) 2 []
  have clearing := clear_executes (71:Fin 96) f
  rw [show f 71=[true] by simp [f,e,d,c,b,a,flag],List.length_singleton] at clearing
  have final : Function.update f 71 []=finishedStore store pool node := by
    funext r
    by_cases n0:r=0 <;> by_cases n1:r=1 <;> by_cases n2:r=2 <;> by_cases n3:r=3 <;>
      by_cases n64:r=64 <;> by_cases n71:r=71 <;>
      simp [finishedStore,internVista,Encoding.vista,Encoding.transport,Encoding.product,Encoding.array,
        f,e,d,c,b,a,R,result,n0,n1,n2,n3,n64,n71,empty]
  rw [final] at clearing
  refine ⟨_,?_,moving.sequence (ri.sequence (clearP.sequence (clearQ.sequence
    (framed.sequence (output.sequence clearing)))))⟩
  have inputP : a 0=P := by simp [a]
  have inputQ : a 1=Q := by simp [a,Q,nodeAt]
  rw [inputP,inputQ] at bi
  dsimp only [finishBudget]
  dsimp only [P,Q,R,result] at *
  omega

end Counting.StackMachine.DagUpdate.Raw
