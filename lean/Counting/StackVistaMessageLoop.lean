import Counting.StackVistaMessageStep

namespace Counting.StackMachine.DagUpdate.Receive
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

abbrev messageLoop : Routine 94 := forEach 76 messageStep

def messageLoopBudget (state : Executable.MergeState) : List (Executable.Vista×Nat) → List Bool → Nat
  | [],_ => 1
  | message::messages,suffix =>
      messageStepBudget state.1 message state.2
        (Encoding.sequence messageCodec (message::messages)++suffix).length+2+
      messageLoopBudget (Executable.mergeMessage state message) messages suffix

def messagesResult (store : Store 94) (state : Executable.MergeState)
    (messages : List (Executable.Vista×Nat)) (suffix : List Bool) : Store 94 :=
  let next := messages.foldl Executable.mergeMessage state
  Function.update (Function.update (Function.update (Function.update store 70 suffix)
    64 ((Encoding.array Encoding.node).encode next.1))
    75 ((Encoding.list edgeCodec).encode next.2)) 76 []

theorem messageLoop_executes (store : Store 94) (state : Executable.MergeState)
    (messages : List (Executable.Vista×Nat)) (suffix : List Bool)
    (source : store 70=Encoding.sequence messageCodec messages++suffix)
    (poolAt : store 64=(Encoding.array Encoding.node).encode state.1)
    (edgesAt : store 75=(Encoding.list edgeCodec).encode state.2)
    (status : store 71=[true])
    (counter : store 76=List.replicate messages.length true)
    (empty : ∀ r : Fin 96,r.val≤73 → r≠64 → r≠70 → r≠71 → store r=[]) :
    ∃ time ≤ messageLoopBudget state messages suffix,
      Executes messageLoop store time (messagesResult store state messages suffix) := by
  induction messages generalizing store state with
  | nil =>
    have counterEmpty : store 76=[] := by simpa using counter
    have sourceAt : store 70=suffix := by simpa [Encoding.sequence] using source
    obtain ⟨run,halt⟩ := repeat_empty (76:Fin 96) messageStep store counterEmpty
    have final : messagesResult store state [] suffix=store := by
      funext r
      by_cases r64 : r=64 <;> by_cases r70 : r=70 <;> by_cases r75 : r=75 <;>
        by_cases r76 : r=76 <;>
        simp [messagesResult,r64,r70,r75,r76,poolAt,edgesAt,sourceAt,counterEmpty]
    exact ⟨1,le_rfl,⟨1,store⟩,run,halt,final.symm⟩
  | cons message messages ih =>
    let consumed := Function.update store 76 (List.replicate messages.length true)
    have consumedEmpty (r : Fin 96) (small : r.val≤73) (n64 : r≠64)
        (n70 : r≠70) (n71 : r≠71) : consumed r=[] := by
      have n76 : r≠76 := by intro eq;subst r;norm_num at small
      simp [consumed,n76,empty r small n64 n70 n71]
    obtain ⟨bodyTime,bodyBound,bodyFinish,bodyRun,bodyHalt,bodyStore⟩ := messageStep_executes
      consumed state message (Encoding.sequence messageCodec messages++suffix)
      (by simpa [consumed,Encoding.sequence,List.append_assoc] using source)
      (by simp [consumed,poolAt]) (by simp [consumed,edgesAt])
      (by simp [consumed,status]) consumedEmpty
    let next := Executable.mergeMessage state message
    let middle := messageResult consumed state message (Encoding.sequence messageCodec messages++suffix)
    have middleEmpty (r : Fin 96) (small : r.val≤73) (n64 : r≠64)
        (n70 : r≠70) (n71 : r≠71) : middle r=[] := by
      have n75 : r≠75 := by intro eq;subst r;norm_num at small
      simp [middle,messageResult,n64,n70,n75,consumedEmpty r small n64 n70 n71]
    obtain ⟨tailTime,tailBound,tailFinish,tailRun,tailHalt,tailStore⟩ := ih middle next
      (by simp [middle,messageResult]) (by simp [middle,messageResult,next])
      (by simp [middle,messageResult,next]) (by simp [middle,messageResult,consumed,status])
      (by simp [middle,messageResult,consumed]) middleEmpty
    have iteration := repeat_iteration (76:Fin 96) messageStep store true
      (List.replicate messages.length true)
      (by simpa only [List.length_cons,List.replicate_succ] using counter)
      bodyTime bodyFinish bodyRun bodyHalt
    have final : messagesResult middle next messages suffix=
        messagesResult store state (message::messages) suffix := by
      funext r
      by_cases r64 : r=64 <;> by_cases r70 : r=70 <;> by_cases r75 : r=75 <;>
        by_cases r76 : r=76 <;>
        simp [messagesResult,middle,messageResult,consumed,next,r64,r70,r75,r76]
    refine ⟨bodyTime+2+tailTime,?_,tailFinish,?_,tailHalt,tailStore.trans final⟩
    · have inputSame : consumed 70=Encoding.sequence messageCodec (message::messages)++suffix := by
        simpa [consumed] using source
      rw [inputSame] at bodyBound
      change _ ≤ messageStepBudget state.1 message state.2
        (Encoding.sequence messageCodec (message::messages)++suffix).length+2+
          messageLoopBudget next messages suffix
      omega
    · rw [Machine.run_add,iteration,Option.bind_some,bodyStore]
      exact tailRun

end Counting.StackMachine.DagUpdate.Receive
