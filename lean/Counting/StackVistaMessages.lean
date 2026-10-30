import Counting.StackVistaMessageLoop
import Counting.StackEncodingListReadHeader

namespace Counting.StackMachine.DagUpdate.Receive
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false

def messagesHeaderRoles : FullListWorkspace 79 :=
  ⟨![70,71,2,3,76,5,6,7,8,9,10,11,12,13,14,15,16],by decide⟩

def messagesHeader : Routine 94 := readListHeader 79 messagesHeaderRoles

theorem messagesHeader_executes (store : Store 94) (messages : List (Executable.Vista×Nat))
    (suffix : List Bool)
    (source : store 70=(Encoding.list messageCodec).encode messages++suffix)
    (status : store 71=[true])
    (empty : ∀ r : Fin 96,(2≤r.val ∧ r.val≤16) ∨ r=76 → store r=[]) :
    ∃ time ≤ 1820*((store 70).length+1)^3,
      Executes messagesHeader store time
        (Function.update (Function.update store 70 (Encoding.sequence messageCodec messages++suffix))
          76 (List.replicate messages.length true)) := by
  apply readListHeader_canonical 79 messagesHeaderRoles store true [] status _ messageCodec _ messages suffix source
  · intro r member
    fin_cases r <;> simp_all [messagesHeaderRoles]
  · intro message
    simp only [messageCodec,Encoding.product,List.length_append,Encoding.natural_length]
    omega

def mergeMessages : Routine 94 := sequence messagesHeader messageLoop

/-- The entire received-message iteration, with its iteration count parsed
from the compact input and bounded against its payload. Multiplicity values
remain binary; the loop visits messages, not repeated individual arcs. -/
theorem mergeMessages_executes (store : Store 94) (state : Executable.MergeState)
    (messages : List (Executable.Vista×Nat)) (suffix : List Bool)
    (source : store 70=(Encoding.list messageCodec).encode messages++suffix)
    (poolAt : store 64=(Encoding.array Encoding.node).encode state.1)
    (edgesAt : store 75=(Encoding.list edgeCodec).encode state.2)
    (status : store 71=[true]) (counterEmpty : store 76=[])
    (empty : ∀ r : Fin 96,r.val≤73 → r≠64 → r≠70 → r≠71 → store r=[]) :
    ∃ time ≤ 1820*((store 70).length+1)^3+1+messageLoopBudget state messages suffix,
      Executes mergeMessages store time (messagesResult store state messages suffix) := by
  obtain ⟨headerTime,headerBound,headerRun⟩ := messagesHeader_executes store messages suffix source status (by
    intro r eligible
    rcases eligible with ⟨lower,upper⟩|rfl
    · apply empty r (by omega)
      · intro eq;subst r;norm_num at upper
      · intro eq;subst r;norm_num at upper
      · intro eq;subst r;norm_num at upper
    · exact counterEmpty)
  let ready := Function.update (Function.update store 70 (Encoding.sequence messageCodec messages++suffix))
    76 (List.replicate messages.length true)
  have readyEmpty (r : Fin 96) (small : r.val≤73) (n64 : r≠64) (n70 : r≠70)
      (n71 : r≠71) : ready r=[] := by
    have n76 : r≠76 := by intro eq;subst r;norm_num at small
    simp [ready,n76,n70,empty r small n64 n70 n71]
  obtain ⟨loopTime,loopBound,loopRun⟩ := messageLoop_executes ready state messages suffix
    (by simp [ready]) (by simp [ready,poolAt]) (by simp [ready,edgesAt])
    (by simp [ready,status]) (by simp [ready]) readyEmpty
  have final : messagesResult ready state messages suffix=messagesResult store state messages suffix := by
    funext r
    by_cases r64 : r=64 <;> by_cases r70 : r=70 <;> by_cases r75 : r=75 <;>
      by_cases r76 : r=76 <;> simp [messagesResult,ready,r64,r70,r75,r76]
  rw [final] at loopRun
  exact ⟨_,by omega,headerRun.sequence loopRun⟩

end Counting.StackMachine.DagUpdate.Receive
