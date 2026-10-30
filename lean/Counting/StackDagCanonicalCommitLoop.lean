import Counting.StackDagCanonicalCommitLoopBody
import Counting.StackEncodingListReadHeader

namespace Counting.StackMachine.DagUpdate.Canonical
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false

def commitHeaderRoles : FullListWorkspace 79 :=
  ⟨![92,81,2,3,93,5,6,7,8,9,10,11,12,13,14,15,16],by decide⟩

def commitHeader : Routine 94 := readListHeader 79 commitHeaderRoles

theorem commitHeader_executes (store : Store 94) (records : List Sort.Record) (suffix : List Bool)
    (source : store 92=(Encoding.list Sort.recordCodec).encode records++suffix)
    (status : store 81=[true])
    (empty : ∀ r : Fin 96,(2 ≤ r.val ∧ r.val ≤ 16) ∨ r=93 → store r=[]) :
    ∃ time ≤ 1820*((store 92).length+1)^3,
      Executes commitHeader store time
        (Function.update (Function.update store 92 (Encoding.sequence Sort.recordCodec records++suffix))
          93 (List.replicate records.length true)) := by
  apply readListHeader_canonical 79 commitHeaderRoles store true [] status _ Sort.recordCodec _ records suffix source
  · intro r member
    fin_cases r <;> simp_all [commitHeaderRoles]
  · intro record
    simp only [Sort.recordCodec,Encoding.product,List.length_append,Encoding.natural_length]
    omega

def commitRecords : Routine 94 := sequence commitHeader commitLoop

/-- The entire canonical insertion fold reads its own iteration count,
interns every sorted signature, updates the mapping and restores scratch. -/
theorem commitRecords_executes (store : Store 94) (state : Executable.CanonicalState)
    (records : List Sort.Record) (suffix : List Bool)
    (inside : ∀ record∈records,record.1 < state.2.size)
    (source : store 92=(Encoding.list Sort.recordCodec).encode records++suffix)
    (mappingAt : store 1=(Encoding.array Encoding.natural).encode state.2)
    (poolAt : store 64=(Encoding.array Encoding.node).encode state.1)
    (status : store 81=[true]) (counterEmpty : store 93=[]) (empty : CommitScratch store) :
    ∃ time ≤ 1820*((store 92).length+1)^3+1+commitLoopBudget state records suffix,
      Executes commitRecords store time (commitLoopResult store state records suffix) := by
  obtain ⟨th,bh,rh⟩ := commitHeader_executes store records suffix source status (by
    intro r eligible
    rcases eligible with ⟨lo,hi⟩|rfl
    · apply empty r (by omega)
      · intro same;subst r;norm_num at lo
      · intro same;subst r;norm_num at hi
    · exact counterEmpty)
  let ready := Function.update (Function.update store 92 (Encoding.sequence Sort.recordCodec records++suffix))
    93 (List.replicate records.length true)
  have readyEmpty : CommitScratch ready := by
    intro r small n1 n64
    have n92 : r≠92 := by intro same;subst r;norm_num at small
    have n93 : r≠93 := by intro same;subst r;norm_num at small
    simp [ready,n92,n93,empty r small n1 n64]
  obtain ⟨tl,bl,rl⟩ := commitLoop_executes ready state records suffix inside
    (by simp [ready]) (by simp [ready,mappingAt]) (by simp [ready,poolAt])
    (by simp [ready,status]) (by simp [ready]) readyEmpty
  have final : commitLoopResult ready state records suffix=commitLoopResult store state records suffix := by
    funext r
    by_cases r1 : r=1 <;> by_cases r64 : r=64 <;> by_cases r92 : r=92 <;>
      by_cases r93 : r=93 <;> simp [commitLoopResult,ready,r1,r64,r92,r93]
  rw [final] at rl
  exact ⟨_,by omega,rh.sequence rl⟩

end Counting.StackMachine.DagUpdate.Canonical
