import Counting.StackDagAddCountStep
import Counting.DagAddCountFold

namespace Counting.StackMachine.DagUpdate
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

theorem edge_sequence_append (first second : List (Nat×Nat)) :
    Encoding.sequence edgeCodec (first++second)=
      Encoding.sequence edgeCodec first++Encoding.sequence edgeCodec second := by
  induction first with
  | nil=>rfl
  | cons edge rest ih=>simp only [List.cons_append,Encoding.sequence,ih,List.append_assoc]

def processEdges (extra : Nat) (w : AddWorkspace extra) : Routine (extra+18) :=
  forEach (w 17) (processEdge extra w)

def loopResult (w : AddWorkspace extra) (store : Store (extra+18))
    (index count : Nat) (pending : Bool) (edges : List (Nat×Nat)) (suffix tail : List Bool) : Store (extra+18) :=
  emittedResult w (Function.update (Function.update store (w 0) suffix) (w 17) [])
    (Counting.DagUpdate.addCountPrefix index count pending edges).1
    (Counting.DagUpdate.addCountPrefix index count pending edges).2 tail

/-- The loop uses the explicit number of sparse entries. Its bound depends
on bit lengths; binary indices and multiplicities never control iteration. -/
theorem processEdges_executes (extra : Nat) (w : AddWorkspace extra) (store : Store (extra+18))
    (index count : Nat) (pending : Bool) (edges : List (Nat×Nat)) (suffix tail : List Bool) (B : Nat)
    (source : store (w 0)=Encoding.sequence edgeCodec edges++suffix)
    (query : store (w 1)=index.bits) (increment : store (w 2)=count.bits)
    (flag : store (w 4)=pending::tail) (counter : store (w 17)=List.replicate edges.length true)
    (empty : ∀ j∈stepScratch,store (w j)=[])
    (bitsBound : ∀ edge∈edges,edge.1.bits.length+edge.2.bits.length ≤ B) :
    ∃ time ≤ edges.length*(110*(index.bits.length+count.bits.length+B)+162)+1,
      Executes (processEdges extra w) store time (loopResult w store index count pending edges suffix tail) := by
  induction edges generalizing store pending with
  | nil=>
    have counterEmpty : store (w 17)=[] := by simpa using counter
    have sourceAt : store (w 0)=suffix := by simpa [Encoding.sequence] using source
    obtain ⟨ran,halted⟩:=repeat_empty (w 17) (processEdge extra w) store counterEmpty
    have same : loopResult w store index count pending [] suffix tail=store := by
      have s0 : Function.update store (w 0) suffix=store := by rw [←sourceAt,Function.update_eq_self]
      have s17 : Function.update store (w 17) []=store := by rw [←counterEmpty,Function.update_eq_self]
      have s6 : Function.update store (w 6) []=store := by rw [←empty 6 (by simp [stepScratch]),Function.update_eq_self]
      have s7 : Function.update store (w 7) []=store := by rw [←empty 7 (by simp [stepScratch]),Function.update_eq_self]
      simp [loopResult,emittedResult,Counting.DagUpdate.addCountPrefix,Encoding.sequence,s0,s17,s6,s7,←flag]
    exact ⟨1,by simp,⟨1,store⟩,ran,halted,same.symm⟩
  | cons edge edges ih=>
    rcases edge with ⟨i,c⟩
    let consumed:=Function.update store (w 17) (List.replicate edges.length true)
    let first:=Counting.DagUpdate.addCountStep index count pending (i,c)
    let next:=emittedResult w (Function.update consumed (w 0)
      (Encoding.sequence edgeCodec edges++suffix)) first.1 first.2 tail
    have consumedEmpty (j : Fin 20) (member : j∈stepScratch) : consumed (w j)=[] := by
      have different : j≠17 := by intro eq;subst j;simp [stepScratch] at member
      simpa [consumed,w.injective.eq_iff,different] using empty j member
    obtain ⟨bodyTime,bodyBound,bodyFinish,bodyRun,bodyHalt,bodyStore⟩:=processEdge_executes extra w consumed
      index count i c pending (Encoding.sequence edgeCodec edges++suffix) tail
      (by simpa [consumed,w.injective.eq_iff,Encoding.sequence,List.append_assoc] using source)
      (by simp [consumed,w.injective.eq_iff,query]) (by simp [consumed,w.injective.eq_iff,increment])
      (by simp [consumed,w.injective.eq_iff,flag]) consumedEmpty
    have nextEmpty (j : Fin 20) (member : j∈stepScratch) : next (w j)=[] := by
      have n0 : j≠0 := by intro eq;subst j;simp [stepScratch] at member
      have n3 : j≠3 := by intro eq;subst j;simp [stepScratch] at member
      have n4 : j≠4 := by intro eq;subst j;simp [stepScratch] at member
      have n5 : j≠5 := by intro eq;subst j;simp [stepScratch] at member
      by_cases n6 : j=6
      · subst j;simp [next,emittedResult,w.injective.eq_iff]
      · by_cases n7 : j=7
        · subst j;simp [next,emittedResult,w.injective.eq_iff]
        · simpa [next,emittedResult,w.injective.eq_iff,n0,n3,n4,n5,n6,n7] using consumedEmpty j member
    obtain ⟨tailTime,tailBound,tailFinish,tailRun,tailHalt,tailStore⟩:=ih next first.2
      (by simp [next,emittedResult,w.injective.eq_iff])
      (by simp [next,emittedResult,consumed,w.injective.eq_iff,query])
      (by simp [next,emittedResult,consumed,w.injective.eq_iff,increment])
      (by simp [next,emittedResult])
      (by simp [next,emittedResult,consumed,w.injective.eq_iff]) nextEmpty
      (fun edge member=>bitsBound edge (by simp [member]))
    have firstRun:=repeat_iteration (w 17) (processEdge extra w) store true (List.replicate edges.length true)
      (by simpa only [List.length_cons,List.replicate_succ] using counter) bodyTime bodyFinish bodyRun bodyHalt
    change Machine.run (step (processEdges extra w).program) (bodyTime+2) ⟨0,store⟩=some ⟨0,bodyFinish.store⟩ at firstRun
    have bodyLimit : bodyTime ≤ 110*(index.bits.length+count.bits.length+B)+160 := by
      have currentBound:=bitsBound (i,c) (by simp)
      change i.bits.length+c.bits.length ≤ B at currentBound
      omega
    refine ⟨bodyTime+2+tailTime,by simp only [List.length_cons];nlinarith only [bodyLimit,tailBound],tailFinish,?_,tailHalt,?_⟩
    · rw [Machine.run_add,firstRun,Option.bind_some,bodyStore]
      exact tailRun
    · rw [tailStore]
      funext r
      by_cases a : r=w 3
      · subst r;simp [loopResult,emittedResult,next,Counting.DagUpdate.addCountPrefix,first,
          edge_sequence_append,List.reverse_append,List.append_assoc,w.injective.eq_iff,consumed]
      · by_cases b : r=w 5
        · subst r
          simp only [loopResult,emittedResult,next,Counting.DagUpdate.addCountPrefix,first,
            Function.update_apply,w.injective.eq_iff,Fin.reduceEq,ite_true,ite_false,List.length_append,consumed]
          rw [←List.append_assoc,List.replicate_append_replicate,Nat.add_comm]
        · by_cases c0 : r=w 0 <;> by_cases c4 : r=w 4 <;> by_cases c6 : r=w 6 <;>
            by_cases c7 : r=w 7 <;> by_cases c17 : r=w 17 <;>
            simp [loopResult,emittedResult,next,Counting.DagUpdate.addCountPrefix,first,consumed,
              a,b,c0,c4,c6,c7,c17]

end Counting.StackMachine.DagUpdate
