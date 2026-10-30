import Counting.StackDagAddCountSelect
import Counting.StackDagAddCountRead

namespace Counting.StackMachine.DagUpdate
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

def processEdge (extra : Nat) (w : AddWorkspace extra) : Routine (extra+18) :=
  sequence (readCurrent extra w) (processCurrent extra w)

def stepScratch : List (Fin 20) := [6,7,8,9,10,11,12,13,14,15,16,19]

theorem processEdge_executes (extra : Nat) (w : AddWorkspace extra) (store : Store (extra+18))
    (index count i c : Nat) (pending : Bool) (suffix tail : List Bool)
    (source : store (w 0)=edgeCodec.encode (i,c)++suffix)
    (query : store (w 1)=index.bits) (increment : store (w 2)=count.bits)
    (flag : store (w 4)=pending::tail) (empty : ∀ j∈stepScratch,store (w j)=[]) :
    ∃ time ≤ 110*(index.bits.length+count.bits.length+i.bits.length+c.bits.length)+160,
      Executes (processEdge extra w) store time
        (emittedResult w (Function.update store (w 0) suffix)
          (Counting.DagUpdate.addCountStep index count pending (i,c)).1
          (Counting.DagUpdate.addCountStep index count pending (i,c)).2 tail) := by
  have reading:=readCurrent_executes extra w store i c suffix source
    (empty 6 (by simp [stepScratch])) (empty 7 (by simp [stepScratch])) (empty 19 (by simp [stepScratch]))
  let read:=Function.update (Function.update (Function.update store (w 0) suffix) (w 6) i.bits) (w 7) c.bits
  have readEmpty (j : Fin 20) (member : j∈actionScratch) : read (w j)=[] := by
    have n0 : j≠0 := by intro eq;subst j;simp [actionScratch] at member
    have n6 : j≠6 := by intro eq;subst j;simp [actionScratch] at member
    have n7 : j≠7 := by intro eq;subst j;simp [actionScratch] at member
    have original : j∈stepScratch := by
      simp only [actionScratch,List.mem_cons,List.not_mem_nil,or_false] at member
      simp only [stepScratch,List.mem_cons,List.not_mem_nil,or_false]
      tauto
    simpa [read,w.injective.eq_iff,n0,n6,n7] using empty j original
  obtain ⟨time,bound,processing⟩:=processCurrent_executes extra w read index count i c pending tail
    (by simp [read,w.injective.eq_iff,query]) (by simp [read,w.injective.eq_iff,increment])
    (by simp [read,w.injective.eq_iff]) (by simp [read]) (by simp [read,w.injective.eq_iff,flag]) readEmpty
  have final : emittedResult w read (Counting.DagUpdate.addCountStep index count pending (i,c)).1
      (Counting.DagUpdate.addCountStep index count pending (i,c)).2 tail=
      emittedResult w (Function.update store (w 0) suffix)
        (Counting.DagUpdate.addCountStep index count pending (i,c)).1
        (Counting.DagUpdate.addCountStep index count pending (i,c)).2 tail := by
    funext r
    by_cases a : r=w 3
    · subst r;simp [emittedResult,read,w.injective.eq_iff]
    · by_cases b : r=w 5
      · subst r;simp [emittedResult,read,w.injective.eq_iff]
      · by_cases d : r=w 6 <;> by_cases e : r=w 7 <;>
          simp [emittedResult,read,Function.update_apply,a,b,d,e]
  rw [final] at processing
  exact ⟨_,by omega,reading.sequence processing⟩

end Counting.StackMachine.DagUpdate
