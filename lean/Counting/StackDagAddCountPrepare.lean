import Counting.StackDagAddCountHeader

namespace Counting.StackMachine.DagUpdate
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false

def prepareEdges (extra : Nat) (w : AddWorkspace extra) : Routine (extra+18) :=
  sequence (pushBit (w 4) true)
    (sequence (readListHeader (extra+3) w.header) (initializePending extra w))

def prepared (w : AddWorkspace extra) (store : Store (extra+18))
    (count : Nat) (edges : List (Nat×Nat)) (suffix : List Bool) : Store (extra+18) :=
  Function.update (Function.update (Function.update store
    (w 0) (Encoding.sequence edgeCodec edges++suffix))
    (w 17) (List.replicate edges.length true)) (w 4) [decide (count≠0)]

theorem prepareEdges_executes (extra : Nat) (w : AddWorkspace extra) (store : Store (extra+18))
    (count : Nat) (edges : List (Nat×Nat)) (suffix : List Bool)
    (source : store (w 0)=(Encoding.list edgeCodec).encode edges++suffix)
    (increment : store (w 2)=count.bits) (flag : store (w 4)=[])
    (empty : ∀ j∈headerScratch,store (w j)=[]) :
    ∃ time ≤ 1820*((store (w 0)).length+1)^3+12,
      Executes (prepareEdges extra w) store time (prepared w store count edges suffix) := by
  have starting:=pushBit_executes (w 4) true store
  rw [flag] at starting
  let started:=Function.update store (w 4) [true]
  have headerEmpty (j : Fin 20) (member : j∈headerScratch) : started (w j)=[] := by
    have ne4 : j≠4 := by intro eq;subst j;simp [headerScratch] at member
    simpa [started,w.injective.eq_iff,ne4] using empty j member
  obtain ⟨headerTime,headerBound,headerRun⟩:=readHeader_executes extra w started edges suffix []
    (by simp [started,w.injective.eq_iff,source]) (by simp [started]) headerEmpty
  let read:=Function.update (Function.update started (w 0) (Encoding.sequence edgeCodec edges++suffix))
    (w 17) (List.replicate edges.length true)
  obtain ⟨pendingTime,pendingBound,pendingRun⟩:=initializePending_executes extra w read count []
    (by simp [read,started,w.injective.eq_iff,increment])
    (by simp [read,started,w.injective.eq_iff])
  have final : Function.update read (w 4) [decide (count≠0)]=prepared w store count edges suffix := by
    funext r
    by_cases a : r=w 4
    · subst r;simp [prepared]
    · simp [read,started,prepared,Function.update_apply,a]
  rw [final] at pendingRun
  have sourceLength : (started (w 0)).length=(store (w 0)).length := by simp [started,w.injective.eq_iff]
  rw [sourceLength] at headerBound
  exact ⟨1+1+(headerTime+1+pendingTime),by omega,starting.sequence (headerRun.sequence pendingRun)⟩

end Counting.StackMachine.DagUpdate
