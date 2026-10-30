import Counting.StackDagCanonicalRead
import Counting.StackLoop

namespace Counting.StackMachine.DagUpdate.Canonical
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

def CommitScratch (store : Store 94) : Prop :=
  ∀ r : Fin 96,r.val ≤ 79 → r≠1 → r≠64 → store r=[]

def commitStep : Routine 94 := sequence readCanonicalRecord (sequence prepareSlot commitSignature)

def commitStepBudget (state : Executable.CanonicalState) (record : Sort.Record) (length : Nat) : Nat :=
  2100*(length+1)^3+
    100*((Sort.recordCodec.encode record).length+
      ((Encoding.array Encoding.natural).encode state.2).length+1)^3+
    commitBudget state record+2

def commitStepResult (store : Store 94) (state : Executable.CanonicalState)
    (record : Sort.Record) (suffix : List Bool) : Store 94 :=
  Function.update (Function.update (Function.update store 92 suffix)
    1 ((Encoding.array Encoding.natural).encode (commitRecord state record).2))
    64 ((Encoding.array Encoding.node).encode (commitRecord state record).1)

theorem commitRecord_mapping_size (state : Executable.CanonicalState) (record : Sort.Record) :
    (commitRecord state record).2.size=state.2.size := by
  simp [commitRecord]

theorem commitStepResult_scratch (store : Store 94) (state : Executable.CanonicalState)
    (record : Sort.Record) (suffix : List Bool) (empty : CommitScratch store) :
    CommitScratch (commitStepResult store state record suffix) := by
  intro r small n1 n64
  have n92 : r≠92 := by intro same;subst r;norm_num at small
  simp [commitStepResult,n92,n1,n64,empty r small n1 n64]

/-- Parse and commit one indexed canonical signature. The original index
selects a mapping slot; the signature itself is interned in the shared pool. -/
theorem commitStep_executes (store : Store 94) (state : Executable.CanonicalState)
    (record : Sort.Record) (suffix : List Bool) (inside : record.1 < state.2.size)
    (source : store 92=Sort.recordCodec.encode record++suffix)
    (mappingAt : store 1=(Encoding.array Encoding.natural).encode state.2)
    (poolAt : store 64=(Encoding.array Encoding.node).encode state.1)
    (status : store 81=[true]) (empty : CommitScratch store) :
    ∃ time ≤ commitStepBudget state record (store 92).length,
      Executes commitStep store time (commitStepResult store state record suffix) := by
  have e0 := empty 0 (by decide) (by decide) (by decide)
  have e75 := empty 75 (by decide) (by decide) (by decide)
  obtain ⟨tr,br,rr⟩ := readCanonicalRecord_executes store record suffix source status e0 (by
    intro r lower upper
    apply empty r (by omega)
    · intro same;subst r;norm_num at lower
    · intro same;subst r;norm_num at upper)
  let read := Function.update (Function.update store 92 suffix) 0 (Sort.recordCodec.encode record)
  have readEmpty (r : Fin 96) (small : r.val ≤ 79) (n0 : r≠0) (n1 : r≠1) (n64 : r≠64) : read r=[] := by
    have n92 : r≠92 := by intro same;subst r;norm_num at small
    simp [read,n0,n92,empty r small n1 n64]
  obtain ⟨ts,bs,rs⟩ := prepareSlot_executes read state.2 record inside
    (by simp [read]) (by simp [read,mappingAt]) (by
      intro r eligible
      rcases eligible with ⟨lo,hi⟩|member
      · apply readEmpty r (by omega) <;> intro same <;> subst r <;> norm_num at *
      · simp only [Finset.mem_insert,Finset.mem_singleton] at member
        rcases member with rfl|rfl|rfl|rfl|rfl <;> apply readEmpty <;> decide)
  let ready := Function.update (Function.update read 0 (Encoding.node.encode record.2))
    75 (List.replicate (record.1+1) true)
  obtain ⟨tc,bc,rc⟩ := commitSignature_executes ready state record inside
    (by simp [ready]) (by simp [ready,read,mappingAt])
    (by simp [ready,read,poolAt]) (by simp [ready]) (by
      intro r eligible
      rcases eligible with ⟨lo,hi⟩|rfl
      · have n0 : r≠0 := by intro same;subst r;norm_num at lo
        have n75 : r≠75 := by intro same;subst r;norm_num at hi
        simp only [ready,Function.update_of_ne n75,Function.update_of_ne n0]
        apply readEmpty r (by omega) n0
        · intro same;subst r;norm_num at lo
        · intro same;subst r;norm_num at hi
      · simpa [ready] using readEmpty 68 (by decide) (by decide) (by decide) (by decide))
  have final : Function.update (Function.update (Function.update (Function.update ready 0 []) 75 [])
      1 ((Encoding.array Encoding.natural).encode (commitRecord state record).2))
      64 ((Encoding.array Encoding.node).encode (commitRecord state record).1)=
      commitStepResult store state record suffix := by
    funext r
    by_cases r0 : r=0 <;> by_cases r1 : r=1 <;> by_cases r64 : r=64 <;>
      by_cases r75 : r=75 <;> by_cases r92 : r=92 <;>
      simp [commitStepResult,ready,read,r0,r1,r64,r75,r92,e0,e75]
  rw [final] at rc
  have readSource : read 0=Sort.recordCodec.encode record := by simp [read]
  have readMapping : read 1=(Encoding.array Encoding.natural).encode state.2 := by simp [read,mappingAt]
  rw [readSource,readMapping] at bs
  refine ⟨_,?_,rr.sequence (rs.sequence rc)⟩
  dsimp only [commitStepBudget]
  omega

end Counting.StackMachine.DagUpdate.Canonical
