import Counting.StackDagCanonicalCollectLoop
import Counting.StackEncodingListReadHeader
import Counting.EncodingVerifier

namespace Counting.StackMachine.DagUpdate.Canonical
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

def collectHeaderRoles : FullListWorkspace 79 :=
  ⟨![0,81,2,3,84,5,6,7,8,9,10,11,12,13,14,15,16],by decide⟩
def collectHeader : Routine 94 := readListHeader 79 collectHeaderRoles

theorem collectHeader_executes (store : Store 94) (nodes : List Executable.Node)
    (source : store 0=(Encoding.list Encoding.node).encode nodes) (status : store 81=[true])
    (empty : CollectScratch store) (counter : store 84=[]) :
    ∃ time ≤ 1820*((store 0).length+1)^3,
      Executes collectHeader store time
        (Function.update (Function.update store 0 (Encoding.sequence Encoding.node nodes))
          84 (List.replicate nodes.length true)) := by
  have ran := readListHeader_canonical 79 collectHeaderRoles store true [] status
    (by
      intro r member
      fin_cases r <;> simp_all [collectHeaderRoles,CollectScratch])
    Encoding.node Encoding.node_positive_length nodes []
    (by simpa [collectHeaderRoles] using source)
  simpa [collectHeader,collectHeaderRoles] using ran

def collectFinishRoles : PowerWorkspace 91 := ⟨![86,85,2,3,4],by decide⟩
def collectFinish : Routine 94 := sequence (emitNatural 91 collectFinishRoles)
  (sequence (clear 83) (clear 86))

theorem collectFinish_executes (store : Store 94) (records : List Sort.Record) (index : Nat)
    (recordsAt : store 85=Encoding.sequence Sort.recordCodec records)
    (countAt : store 86=List.replicate records.length true)
    (indexAt : store 83=List.replicate index true)
    (empty : CollectScratch store) :
    ∃ time ≤ 20*(records.length+1)^2+index+records.length+4,
      Executes collectFinish store time
        (Function.update (Function.update (Function.update store
          85 ((Encoding.list Sort.recordCodec).encode records)) 83 []) 86 []) := by
  obtain ⟨t,b,r⟩ := emitNatural_executes 91 collectFinishRoles store
    (empty 2 (by decide) (by decide) (by decide))
    (empty 3 (by decide) (by decide) (by decide))
    (empty 4 (by decide) (by decide) (by decide))
  change t ≤ 20*((store 86).length+1)^2 at b
  change Executes (emitNatural 91 collectFinishRoles) store t
    (Function.update store 85 (Encoding.natural.encode (store 86).length++store 85)) at r
  rw [countAt,List.length_replicate,recordsAt] at r
  rw [countAt,List.length_replicate] at b
  let a := Function.update store 85 ((Encoding.list Sort.recordCodec).encode records)
  have clearIndex := clear_executes (83:Fin 96) a
  rw [show a 83=List.replicate index true by simp [a,indexAt],List.length_replicate] at clearIndex
  let middle := Function.update a 83 []
  have clearCount := clear_executes (86:Fin 96) middle
  rw [show middle 86=List.replicate records.length true by simp [middle,a,countAt],List.length_replicate] at clearCount
  exact ⟨_,by omega,r.sequence (clearIndex.sequence clearCount)⟩

def collectRecords : Routine 94 := sequence collectHeader (sequence collectLoop collectFinish)

def collectedStore (store : Store 94) (mapping : Array Nat) (nodes : List Executable.Node) (level : Nat) : Store 94 :=
  Function.update (Function.update store 0 []) 85
    ((Encoding.list Sort.recordCodec).encode (collectEntries mapping level 0 nodes).reverse)

/-- Build precisely the reversed original-index record list expected by
stable canonical sorting, preserving the frozen map and every other field. -/
theorem collectRecords_executes (store : Store 94) (mapping : Array Nat) (nodes : List Executable.Node)
    (level : Nat) (source : store 0=(Encoding.list Encoding.node).encode nodes)
    (mapAt : store 1=(Encoding.array Encoding.natural).encode mapping)
    (levelAt : store 82=level.bits) (status : store 81=[true])
    (index : store 83=[]) (counter : store 84=[]) (records : store 85=[]) (count : store 86=[])
    (empty : CollectScratch store) :
    ∃ time ≤ 1820*((store 0).length+1)^3+1+
      (collectLoopBudget mapping level 0 nodes []+1+
        (20*((collectEntries mapping level 0 nodes).length+1)^2+
          nodes.length+(collectEntries mapping level 0 nodes).length+4)),
      Executes collectRecords store time (collectedStore store mapping nodes level) := by
  obtain ⟨th,bh,rh⟩ := collectHeader_executes store nodes source status empty counter
  let ready := Function.update (Function.update store 0 (Encoding.sequence Encoding.node nodes))
    84 (List.replicate nodes.length true)
  have readyEmpty : CollectScratch ready := by
    intro r lo hi n64
    have n0 : r≠0 := by intro eq;subst r;omega
    have n84 : r≠84 := by intro eq;subst r;omega
    simp [ready,n0,n84,empty r lo hi n64]
  obtain ⟨tl,bl,rl⟩ := collectLoop_executes ready mapping nodes [] 0 level
    (by simp [ready]) (by simp [ready,mapAt]) (by simp [ready,index])
    (by simp [ready,levelAt]) (by simp [ready]) readyEmpty
  let result := collectLoopResult ready mapping nodes [] 0 level
  have resultEmpty : CollectScratch result := by
    intro r lo hi n64
    have n0 : r≠0 := by intro eq;subst r;omega
    have n83 : r≠83 := by intro eq;subst r;omega
    have n84 : r≠84 := by intro eq;subst r;omega
    have n85 : r≠85 := by intro eq;subst r;omega
    have n86 : r≠86 := by intro eq;subst r;omega
    simp [result,collectLoopResult,n0,n83,n84,n85,n86,readyEmpty r lo hi n64]
  obtain ⟨tf,bf,rf⟩ := collectFinish_executes result
    (collectEntries mapping level 0 nodes).reverse nodes.length
    (by simp [result,collectLoopResult,ready,records])
    (by simp [result,collectLoopResult,ready,count])
    (by simp [result,collectLoopResult]) resultEmpty
  have final : Function.update (Function.update (Function.update result
      85 ((Encoding.list Sort.recordCodec).encode (collectEntries mapping level 0 nodes).reverse)) 83 []) 86 []=
      collectedStore store mapping nodes level := by
    funext r
    by_cases r0 : r=0 <;> by_cases r83 : r=83 <;> by_cases r84 : r=84 <;>
      by_cases r85 : r=85 <;> by_cases r86 : r=86 <;>
      simp [result,collectLoopResult,collectedStore,ready,r0,r83,r84,r85,r86,index,counter,count]
  rw [final] at rf
  simp only [List.length_reverse] at bf
  exact ⟨_,by omega,rh.sequence (rl.sequence rf)⟩

end Counting.StackMachine.DagUpdate.Canonical
