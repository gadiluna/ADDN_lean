import Counting.StackDagCanonicalCommitLoopStep

namespace Counting.StackMachine.DagUpdate.Canonical
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

abbrev commitLoop : Routine 94 := forEach 93 commitStep

def commitLoopBudget (state : Executable.CanonicalState) : List Sort.Record → List Bool → Nat
  | [],_ => 1
  | record::records,suffix =>
      commitStepBudget state record (Encoding.sequence Sort.recordCodec (record::records)++suffix).length+2+
      commitLoopBudget (commitRecord state record) records suffix

def commitLoopResult (store : Store 94) (state : Executable.CanonicalState)
    (records : List Sort.Record) (suffix : List Bool) : Store 94 :=
  let next := records.foldl commitRecord state
  Function.update (Function.update (Function.update (Function.update store 92 suffix)
    1 ((Encoding.array Encoding.natural).encode next.2))
    64 ((Encoding.array Encoding.node).encode next.1)) 93 []

theorem commitLoop_executes (store : Store 94) (state : Executable.CanonicalState)
    (records : List Sort.Record) (suffix : List Bool)
    (inside : ∀ record∈records,record.1 < state.2.size)
    (source : store 92=Encoding.sequence Sort.recordCodec records++suffix)
    (mappingAt : store 1=(Encoding.array Encoding.natural).encode state.2)
    (poolAt : store 64=(Encoding.array Encoding.node).encode state.1)
    (status : store 81=[true]) (counter : store 93=List.replicate records.length true)
    (empty : CommitScratch store) :
    ∃ time ≤ commitLoopBudget state records suffix,
      Executes commitLoop store time (commitLoopResult store state records suffix) := by
  induction records generalizing store state with
  | nil =>
    have counterEmpty : store 93=[] := by simpa using counter
    have sourceAt : store 92=suffix := by simpa [Encoding.sequence] using source
    obtain ⟨run,halt⟩ := repeat_empty (93:Fin 96) commitStep store counterEmpty
    have final : commitLoopResult store state [] suffix=store := by
      funext r
      by_cases r1 : r=1 <;> by_cases r64 : r=64 <;> by_cases r92 : r=92 <;>
        by_cases r93 : r=93 <;>
        simp [commitLoopResult,r1,r64,r92,r93,mappingAt,poolAt,sourceAt,counterEmpty]
    exact ⟨1,le_rfl,⟨1,store⟩,run,halt,final.symm⟩
  | cons record records ih =>
    let consumed := Function.update store 93 (List.replicate records.length true)
    have consumedEmpty : CommitScratch consumed := by
      intro r small n1 n64
      have n93 : r≠93 := by intro same;subst r;norm_num at small
      simp [consumed,n93,empty r small n1 n64]
    obtain ⟨bodyTime,bodyBound,bodyFinish,bodyRun,bodyHalt,bodyStore⟩ := commitStep_executes
      consumed state record (Encoding.sequence Sort.recordCodec records++suffix) (inside record (by simp))
      (by simpa [consumed,Encoding.sequence,List.append_assoc] using source)
      (by simp [consumed,mappingAt]) (by simp [consumed,poolAt])
      (by simp [consumed,status]) consumedEmpty
    let next := commitRecord state record
    let middle := commitStepResult consumed state record (Encoding.sequence Sort.recordCodec records++suffix)
    obtain ⟨tailTime,tailBound,tailFinish,tailRun,tailHalt,tailStore⟩ := ih middle next
      (by intro other member;simpa [next,commitRecord_mapping_size] using inside other (by simp [member]))
      (by simp [middle,commitStepResult]) (by simp [middle,commitStepResult,next])
      (by simp [middle,commitStepResult,next]) (by simp [middle,commitStepResult,consumed,status])
      (by simp [middle,commitStepResult,consumed])
      (commitStepResult_scratch consumed state record _ consumedEmpty)
    have iteration := repeat_iteration (93:Fin 96) commitStep store true
      (List.replicate records.length true)
      (by simpa only [List.length_cons,List.replicate_succ] using counter)
      bodyTime bodyFinish bodyRun bodyHalt
    have final : commitLoopResult middle next records suffix=
        commitLoopResult store state (record::records) suffix := by
      funext r
      by_cases r1 : r=1 <;> by_cases r64 : r=64 <;> by_cases r92 : r=92 <;>
        by_cases r93 : r=93 <;>
        simp [commitLoopResult,middle,commitStepResult,consumed,next,r1,r64,r92,r93]
    refine ⟨bodyTime+2+tailTime,?_,tailFinish,?_,tailHalt,tailStore.trans final⟩
    · have same : consumed 92=Encoding.sequence Sort.recordCodec (record::records)++suffix := by
        simpa [consumed] using source
      rw [same] at bodyBound
      change _ ≤ commitStepBudget state record (Encoding.sequence Sort.recordCodec (record::records)++suffix).length+
        2+commitLoopBudget next records suffix
      omega
    · rw [Machine.run_add,iteration,Option.bind_some,bodyStore]
      exact tailRun

end Counting.StackMachine.DagUpdate.Canonical
