import Counting.StackDagAddCountLoop
import Counting.StackDagAddCountFlush

namespace Counting.StackMachine.DagUpdate
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

def processAndFlush (extra : Nat) (w : AddWorkspace extra) : Routine (extra+18) :=
  sequence (processEdges extra w) (flushPending extra w)

def bodyResult (w : AddWorkspace extra) (store : Store (extra+18))
    (edges : List (Nat×Nat)) (suffix tail : List Bool) : Store (extra+18) :=
  Function.update (Function.update (Function.update (Function.update (Function.update store
    (w 0) suffix) (w 17) []) (w 3) (Encoding.sequence edgeCodec edges).reverse)
    (w 5) (List.replicate edges.length true)) (w 4) tail

/-- Complete the sparse-entry scan, including the final pending insertion.
This contract holds for arbitrary sparse lists, without an ordering premise. -/
theorem processAndFlush_executes (extra : Nat) (w : AddWorkspace extra) (store : Store (extra+18))
    (index count : Nat) (pending : Bool) (edges : List (Nat×Nat)) (suffix tail : List Bool) (B : Nat)
    (source : store (w 0)=Encoding.sequence edgeCodec edges++suffix)
    (query : store (w 1)=index.bits) (increment : store (w 2)=count.bits)
    (flag : store (w 4)=pending::tail) (counter : store (w 17)=List.replicate edges.length true)
    (output : store (w 3)=[]) (lengthEmpty : store (w 5)=[])
    (empty : ∀ j∈stepScratch,store (w j)=[])
    (bitsBound : ∀ edge∈edges,edge.1.bits.length+edge.2.bits.length ≤ B) :
    ∃ time ≤ edges.length*(110*(index.bits.length+count.bits.length+B)+162)+
        14*(index.bits.length+count.bits.length)+28,
      Executes (processAndFlush extra w) store time
        (bodyResult w store (Counting.DagUpdate.addCountEntries index count pending edges) suffix tail) := by
  obtain ⟨loopTime,loopBound,loopRun⟩:=processEdges_executes extra w store index count pending edges
    suffix tail B source query increment flag counter empty bitsBound
  let result:=Counting.DagUpdate.addCountPrefix index count pending edges
  let scanned:=loopResult w store index count pending edges suffix tail
  have scannedEmpty (j : Fin 20) (member : j∈([8,9,10,15,16]:List (Fin 20))) : scanned (w j)=[] := by
    have ne0 : j≠0 := by intro eq;subst j;simp at member
    have ne3 : j≠3 := by intro eq;subst j;simp at member
    have ne4 : j≠4 := by intro eq;subst j;simp at member
    have ne5 : j≠5 := by intro eq;subst j;simp at member
    have ne6 : j≠6 := by intro eq;subst j;simp at member
    have ne7 : j≠7 := by intro eq;subst j;simp at member
    have ne17 : j≠17 := by intro eq;subst j;simp at member
    simpa [scanned,loopResult,emittedResult,w.injective.eq_iff,ne0,ne3,ne4,ne5,ne6,ne7,ne17]
      using empty j (by simp only [List.mem_cons,List.not_mem_nil,or_false] at member; rcases member with h|h|h|h|h <;> subst j <;> simp [stepScratch])
  obtain ⟨flushTime,flushBound,flushRun⟩:=flushPending_executes extra w scanned index count result.2 tail
    (by simp [scanned,loopResult,emittedResult,w.injective.eq_iff,query])
    (by simp [scanned,loopResult,emittedResult,w.injective.eq_iff,increment])
    (by simp [scanned,loopResult,emittedResult,result]) scannedEmpty
  have final : flushResult w scanned index count result.2 tail=
      bodyResult w store (Counting.DagUpdate.addCountEntries index count pending edges) suffix tail := by
    rw [←Counting.DagUpdate.addCountPrefix_flush]
    change flushResult w scanned index count result.2 tail=
      bodyResult w store (result.1++(if result.2 then [(index,count)] else [])) suffix tail
    funext r
    by_cases r3 : r=w 3
    · subst r
      simp [flushResult,scanned,loopResult,emittedResult,bodyResult,result,
        edge_sequence_append,List.reverse_append,w.injective.eq_iff,output]
    · by_cases r5 : r=w 5
      · subst r
        simp only [flushResult,scanned,loopResult,emittedResult,bodyResult,result,
          Function.update_apply,w.injective.eq_iff,Fin.reduceEq,ite_true,ite_false,lengthEmpty,
          List.append_nil,List.length_append]
        rw [List.replicate_append_replicate,Nat.add_comm]
      · by_cases r6 : r=w 6
        · subst r;simp [flushResult,scanned,loopResult,emittedResult,bodyResult,w.injective.eq_iff,
            empty 6 (by simp [stepScratch])]
        · by_cases r7 : r=w 7
          · subst r;simp [flushResult,scanned,loopResult,emittedResult,bodyResult,w.injective.eq_iff,
              empty 7 (by simp [stepScratch])]
          · by_cases r0 : r=w 0 <;> by_cases r4 : r=w 4 <;> by_cases r17 : r=w 17 <;>
              simp [flushResult,scanned,loopResult,emittedResult,bodyResult,
                r3,r5,r6,r7,r0,r4,r17]
  rw [final] at flushRun
  exact ⟨loopTime+1+flushTime,by omega,loopRun.sequence flushRun⟩

end Counting.StackMachine.DagUpdate
