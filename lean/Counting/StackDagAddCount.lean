import Counting.StackDagAddCountPrepare
import Counting.StackDagAddCountBody
import Counting.StackDagAddCountFinish

namespace Counting.StackMachine.DagUpdate
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

/-- Update a compact encoded sparse list. Only its explicit entry count
controls iteration; both the index and the multiplicity remain binary. -/
def addCount (extra : Nat) (w : AddWorkspace extra) : Routine (extra+18) :=
  sequence (prepareEdges extra w) (sequence (processAndFlush extra w) (finishEdges extra w))

def addCountBudget (index count : Nat) (edges : List (Nat×Nat)) (sourceLength B : Nat) : Nat :=
  let output:=Executable.addCount index count edges
  1820*(sourceLength+1)^3+
    edges.length*(110*(index.bits.length+count.bits.length+B)+162)+
    14*(index.bits.length+count.bits.length)+
    40*((Encoding.sequence edgeCodec output).length+output.length+1)^2+42

/-- Exact full-store refinement of `Executable.addCount`, including zero
increments, repeated indices, unsorted lists and a preserved input suffix. -/
theorem addCount_executes (extra : Nat) (w : AddWorkspace extra) (store : Store (extra+18))
    (index count : Nat) (edges : List (Nat×Nat)) (suffix : List Bool) (B : Nat)
    (source : store (w 0)=(Encoding.list edgeCodec).encode edges++suffix)
    (query : store (w 1)=index.bits) (increment : store (w 2)=count.bits)
    (empty : ∀ j : Fin 20,j≠0 → j≠1 → j≠2 → store (w j)=[])
    (bitsBound : ∀ edge∈edges,edge.1.bits.length+edge.2.bits.length ≤ B) :
    ∃ time ≤ addCountBudget index count edges (store (w 0)).length B,
      Executes (addCount extra w) store time
        (Function.update (Function.update store (w 0) suffix) (w 3)
          ((Encoding.list edgeCodec).encode (Executable.addCount index count edges))) := by
  have headerEmpty (j : Fin 20) (member : j∈headerScratch) : store (w j)=[] := by
    apply empty j <;> intro eq <;> subst j <;> simp [headerScratch] at member
  obtain ⟨prepareTime,prepareBound,preparing⟩:=prepareEdges_executes extra w store count edges suffix
    source increment (empty 4 (by decide) (by decide) (by decide)) headerEmpty
  let ready:=prepared w store count edges suffix
  have readyEmpty (j : Fin 20) (member : j∈stepScratch) : ready (w j)=[] := by
    have ne0 : j≠0 := by intro eq;subst j;simp [stepScratch] at member
    have ne1 : j≠1 := by intro eq;subst j;simp [stepScratch] at member
    have ne2 : j≠2 := by intro eq;subst j;simp [stepScratch] at member
    have ne4 : j≠4 := by intro eq;subst j;simp [stepScratch] at member
    have ne17 : j≠17 := by intro eq;subst j;simp [stepScratch] at member
    simpa [ready,prepared,w.injective.eq_iff,ne0,ne4,ne17] using empty j ne0 ne1 ne2
  obtain ⟨bodyTime,bodyBound,bodyRun⟩:=processAndFlush_executes extra w ready index count
    (decide (count≠0)) edges suffix [] B
    (by simp [ready,prepared,w.injective.eq_iff])
    (by simp [ready,prepared,w.injective.eq_iff,query])
    (by simp [ready,prepared,w.injective.eq_iff,increment])
    (by simp [ready,prepared]) (by simp [ready,prepared,w.injective.eq_iff])
    (by simp [ready,prepared,w.injective.eq_iff,empty])
    (by simp [ready,prepared,w.injective.eq_iff,empty]) readyEmpty bitsBound
  rw [Counting.DagUpdate.addCountEntries_exact] at bodyRun
  let output:=Executable.addCount index count edges
  let scanned:=bodyResult w ready output suffix []
  have scannedEmpty (j : Fin 20) (member : j∈([6,7,18,19]:List (Fin 20))) : scanned (w j)=[] := by
    have ne0 : j≠0 := by intro eq;subst j;simp at member
    have ne1 : j≠1 := by intro eq;subst j;simp at member
    have ne2 : j≠2 := by intro eq;subst j;simp at member
    have ne3 : j≠3 := by intro eq;subst j;simp at member
    have ne4 : j≠4 := by intro eq;subst j;simp at member
    have ne5 : j≠5 := by intro eq;subst j;simp at member
    have ne17 : j≠17 := by intro eq;subst j;simp at member
    simpa [scanned,bodyResult,ready,prepared,w.injective.eq_iff,ne0,ne3,ne4,ne5,ne17]
      using empty j ne0 ne1 ne2
  obtain ⟨finishTime,finishBound,finishing⟩:=finishEdges_executes extra w scanned output
    (by simp [scanned,bodyResult,w.injective.eq_iff])
    (by simp [scanned,bodyResult,w.injective.eq_iff]) scannedEmpty
  have final : Function.update (Function.update scanned (w 3) ((Encoding.list edgeCodec).encode output)) (w 5) []=
      Function.update (Function.update store (w 0) suffix) (w 3) ((Encoding.list edgeCodec).encode output) := by
    funext r
    by_cases r4 : r=w 4
    · subst r;simp [scanned,bodyResult,w.injective.eq_iff,empty]
    · by_cases r5 : r=w 5
      · subst r;simp [w.injective.eq_iff,empty]
      · by_cases r17 : r=w 17
        · subst r;simp [scanned,bodyResult,w.injective.eq_iff,empty]
        · by_cases r0 : r=w 0 <;> by_cases r3 : r=w 3 <;>
            simp [scanned,bodyResult,ready,prepared,r0,r3,r4,r5,r17]
  rw [final] at finishing
  exact ⟨prepareTime+1+(bodyTime+1+finishTime),by dsimp only [output] at finishBound; dsimp only [addCountBudget];omega,
    preparing.sequence (bodyRun.sequence finishing)⟩

end Counting.StackMachine.DagUpdate
