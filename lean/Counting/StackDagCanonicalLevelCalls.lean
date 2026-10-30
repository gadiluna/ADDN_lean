import Counting.StackDagCanonicalCollectEncoding
import Counting.StackDagCanonicalCommitLoopPolynomial
import Counting.StackDagSortComplete
import Counting.StackRealizabilityExternalFields
import Counting.StackRegisterFrames
import Counting.DagCanonicalCollectSpec

namespace Counting.StackMachine.DagUpdate.Canonical
open Routine RealizabilityCall Executable
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

def levelCollectRoles : Fin 96 ↪ Fin 130 where
  toFun i := ![127,101,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,128,122,83,84,126,86,87,88,89,90,91,92,93,94,95] i
  inj' := by decide
def levelCollect : Routine 128 := relocate collectRecords levelCollectRoles

theorem levelCollect_executes (data : Fin 30 → List Bool)
    (source : Vista) (mapping : Array Nat) (level : Nat)
    (sourceAt : data 27=(Encoding.array Encoding.node).encode source.nodes)
    (mapAt : data 1=(Encoding.array Encoding.natural).encode mapping)
    (levelAt : data 22=level.bits) (flag : data 28=[true]) (vacant : data 26=[]) :
    ∃ time ≤ collectCoefficient*((data 27).length+(data 1).length+(data 22).length+1)^8,
      Executes levelCollect (file data) time
        (file (Function.update (Function.update data 27 []) 26
          ((Encoding.list Sort.recordCodec).encode (collectEntries mapping level 0 source.nodes.toList).reverse))) := by
  let store := file data ∘ levelCollectRoles
  obtain ⟨time,bound,ran⟩ := collectRecords_polynomial store mapping source.nodes.toList level
    (by simpa [store,levelCollectRoles,file,Encoding.array,Encoding.transport] using sourceAt)
    (by simpa [store,levelCollectRoles,file] using mapAt)
    (by simpa [store,levelCollectRoles,file] using levelAt)
    (by simpa [store,levelCollectRoles,file] using flag)
    (by simp [store,levelCollectRoles,file]) (by simp [store,levelCollectRoles,file])
    (by simpa [store,levelCollectRoles,file] using vacant)
    (by simp [store,levelCollectRoles,file])
    (by intro r low high n64;fin_cases r <;> simp_all [store,levelCollectRoles,file])
  have wide := relocate_executes collectRecords levelCollectRoles (file data) time _ ran
  simp only [collectedStore,store,relocatedStore_update,relocatedStore_original] at wide
  have a : levelCollectRoles 0=context 27 := by simp [levelCollectRoles,context]
  have b : levelCollectRoles 85=context 26 := by simp [levelCollectRoles,context]
  rw [a,b,file_update,file_update] at wide
  refine ⟨time,?_,wide⟩
  simpa [store,levelCollectRoles,file] using bound

def levelSortRoles : Fin 96 ↪ Fin 130 where
  toFun i := ![126,129,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95] i
  inj' := by decide
def levelSort : Routine 128 := relocate Sort.completeSort levelSortRoles

theorem levelSort_executes (data : Fin 30 → List Bool) (records : List Sort.Record)
    (sourceAt : data 26=Sort.sortInput records) (vacant : data 29=[]) :
    ∃ time ≤ 30000*((data 26).length+1)^5,
      Executes levelSort (file data) time
        (file (Function.update (Function.update data 26 []) 29 (Sort.sortOutput records))) := by
  obtain ⟨time,bound,ran⟩ := Sort.completeSort_executes records
  have initial : file data ∘ levelSortRoles=inputStore 94 (Sort.sortInput records) := by
    funext r;fin_cases r <;> simp [levelSortRoles,file,inputStore,sourceAt,vacant]
  rw [←initial] at ran
  have final : outputStore 94 (Sort.sortOutput records)=
      Function.update (Function.update (file data ∘ levelSortRoles) 0 []) 1 (Sort.sortOutput records) := by
    rw [initial]
    funext r
    by_cases r0:r=0 <;> by_cases r1:r=1 <;> simp [outputStore,inputStore,r0,r1]
  rw [final] at ran
  have wide := relocate_executes Sort.completeSort levelSortRoles (file data) time _ ran
  rw [relocatedStore_update,relocatedStore_update,relocatedStore_original] at wide
  have a : levelSortRoles 0=context 26 := by simp [levelSortRoles,context]
  have b : levelSortRoles 1=context 29 := by simp [levelSortRoles,context]
  rw [a,b,file_update,file_update] at wide
  exact ⟨time,by simpa [sourceAt] using bound,wide⟩

def levelCommitRoles : Fin 96 ↪ Fin 130 where
  toFun i := ![0,101,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,102,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,128,82,83,84,85,86,87,88,89,90,91,129,93,94,95] i
  inj' := by decide
def levelCommit : Routine 128 := relocate commitRecords levelCommitRoles

def levelCommittedData (data : Fin 30 → List Bool) (state : CanonicalState) : Fin 30 → List Bool :=
  Function.update (Function.update (Function.update data
    1 ((Encoding.array Encoding.natural).encode state.2))
    2 ((Encoding.array Encoding.node).encode state.1)) 29 []

theorem levelCommit_executes (data : Fin 30 → List Bool) (state : CanonicalState)
    (records : List Sort.Record) (inside : ∀ record∈records,record.1 < state.2.size)
    (sourceAt : data 29=(Encoding.list Sort.recordCodec).encode records)
    (mapAt : data 1=(Encoding.array Encoding.natural).encode state.2)
    (poolAt : data 2=(Encoding.array Encoding.node).encode state.1) (flag : data 28=[true]) :
    ∃ time ≤ commitRecordsCoefficient*((data 2).length+(data 1).length+(data 29).length+1)^9,
      Executes levelCommit (file data) time (file (levelCommittedData data (records.foldl commitRecord state))) := by
  let store := file data ∘ levelCommitRoles
  obtain ⟨time,bound,ran⟩ := commitRecords_polynomial store state records [] inside
    (by simpa [store,levelCommitRoles,file] using sourceAt)
    (by simpa [store,levelCommitRoles,file] using mapAt)
    (by simpa [store,levelCommitRoles,file] using poolAt)
    (by simpa [store,levelCommitRoles,file] using flag)
    (by simp [store,levelCommitRoles,file])
    (by intro r low n1 n64;fin_cases r <;> simp_all [store,levelCommitRoles,file])
  have wide := relocate_executes commitRecords levelCommitRoles (file data) time _ ran
  simp only [commitLoopResult,store,relocatedStore_update,relocatedStore_original] at wide
  have a : levelCommitRoles 92=context 29 := by simp [levelCommitRoles,context]
  have b : levelCommitRoles 1=context 1 := by simp [levelCommitRoles,context]
  have c : levelCommitRoles 64=context 2 := by simp [levelCommitRoles,context]
  have d : levelCommitRoles 93=93 := by simp [levelCommitRoles]
  rw [a,b,c,d,file_update,file_update,file_update] at wide
  have clean : Function.update (file (Function.update (Function.update (Function.update data 29 [])
      1 ((Encoding.array Encoding.natural).encode (records.foldl commitRecord state).2))
      2 ((Encoding.array Encoding.node).encode (records.foldl commitRecord state).1))) 93 [] =
      file (levelCommittedData data (records.foldl commitRecord state)) := by
    funext r
    by_cases r93:r=93
    · subst r;simp [file]
    · simp only [Function.update_of_ne r93]
      congr 1
      funext i
      by_cases i1:i=1 <;> by_cases i2:i=2 <;> by_cases i29:i=29 <;>
        simp [levelCommittedData,i1,i2,i29]
  rw [clean] at wide
  exact ⟨time,by simpa [store,levelCommitRoles,file] using bound,wide⟩

end Counting.StackMachine.DagUpdate.Canonical

