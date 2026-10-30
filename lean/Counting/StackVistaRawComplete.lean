import Counting.StackVistaRawPrepare
import Counting.StackVistaRawAssemble
import Counting.StackVistaRawFinish
import Counting.DagRawIdentity

namespace Counting.StackMachine.DagUpdate.Raw
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option maxRecDepth 10000

def updated (round : Nat) (leader : Bool) (degree : Nat) (old : Executable.Vista)
    (messages : List (Executable.Vista×Nat)) : Executable.Vista :=
  let merged := messages.foldl Executable.mergeMessage (old.nodes,[])
  internVista merged.1 (newNode round old.bottom leader degree merged.2)

def complete : Routine 94 := sequence prepare
  (sequence Receive.mergeMessages (sequence incrementAndAssemble finish))

def completeBudget (round : Nat) (leader : Bool) (degree : Nat) (old : Executable.Vista)
    (messages : List (Executable.Vista×Nat)) : Nat :=
  let merged := messages.foldl Executable.mergeMessage (old.nodes,[])
  prepareBudget round degree old messages+
    1820*(((Encoding.list Receive.messageCodec).encode messages).length+1)^3+
    Receive.messageLoopBudget (old.nodes,[]) messages []+
    assembleBudget round old.bottom leader degree merged.2+
    finishBudget merged.1 (newNode round old.bottom leader degree merged.2)+4

/-- A closed binary receiver update. All parsing, message import, count
aggregation, metadata arithmetic, node construction, interning and cleanup
are executed instructions. The result is specified for every typed input. -/
theorem complete_executes (round : Nat) (leader : Bool) (degree : Nat) (old : Executable.Vista)
    (messages : List (Executable.Vista×Nat)) :
    ∃ time ≤ completeBudget round leader degree old messages,
      Executes complete (inputStore 94 (inputWord round leader degree old messages)) time
        (outputStore 94 (Encoding.vista.encode (updated round leader degree old messages))) := by
  obtain ⟨tp,bp,rp⟩ := prepare_executes round leader degree old messages
  let ready := preparedStore round leader degree old messages
  let merged := messages.foldl Executable.mergeMessage (old.nodes,[])
  let node := newNode round old.bottom leader degree merged.2
  obtain ⟨tm,bm,rm⟩ := Receive.mergeMessages_executes ready (old.nodes,[]) messages []
    (by simp [ready,preparedStore]) (by simp [ready,preparedStore])
    (by simp [ready,preparedStore,edgeCodec,Encoding.list,Encoding.natural,Encoding.sequence,Encoding.frame])
    (by simp [ready,preparedStore,labelsStore]) (by simp [ready,preparedStore,labelsStore]) (by
      intro r small n64 n70 n71
      have n75:r≠75 := by intro eq;subst r;norm_num at small
      have n80:r≠80 := by intro eq;subst r;norm_num at small
      have n81:r≠81 := by intro eq;subst r;norm_num at small
      have n82:r≠82 := by intro eq;subst r;norm_num at small
      have n83:r≠83 := by intro eq;subst r;norm_num at small
      simp [ready,preparedStore,labelsStore,n64,n70,n71,n75,n80,n81,n82,n83])
  let imported := Receive.messagesResult ready (old.nodes,[]) messages []
  obtain ⟨ta,ba,ra⟩ := incrementAndAssemble_executes imported round old.bottom leader degree merged.2
    (by simp [imported,Receive.messagesResult,ready,preparedStore,labelsStore])
    (by simp [imported,Receive.messagesResult,ready,preparedStore])
    (by simp [imported,Receive.messagesResult,ready,preparedStore,labelsStore])
    (by simp [imported,Receive.messagesResult,ready,preparedStore,labelsStore])
    (by simp [imported,Receive.messagesResult,merged,edgeCodec]) (by
      intro r eligible
      rcases eligible with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        simp [imported,Receive.messagesResult,ready,preparedStore,labelsStore])
  let assembled := assembledStore imported node
  obtain ⟨tf,bf,rf⟩ := finish_executes assembled merged.1 node
    (by simp [assembled,assembledStore,imported,Receive.messagesResult,merged])
    (by simp [assembled,assembledStore])
    (by simp [assembled,assembledStore,imported,Receive.messagesResult,ready,preparedStore,labelsStore]) (by
      intro r eligible
      rcases eligible with rfl|⟨lo,hi⟩|rfl
      · simp [assembled,assembledStore,imported,Receive.messagesResult,ready,preparedStore,labelsStore]
      · have n1:r≠1 := by intro eq;subst r;norm_num at lo
        have high : ∀ j:Fin 96,37<j.val → r≠j := by
          intro j big eq
          have equal := congrArg (fun k:Fin 96=>k.val) eq
          omega
        simp [assembled,assembledStore,imported,Receive.messagesResult,ready,preparedStore,labelsStore,
          n1,high 64 (by decide),high 70 (by decide),high 71 (by decide),high 75 (by decide),
          high 76 (by decide),high 80 (by decide),high 81 (by decide),high 82 (by decide),high 83 (by decide)]
      · simp [assembled,assembledStore,imported,Receive.messagesResult,ready,preparedStore,labelsStore])
  have final : finishedStore assembled merged.1 node=
      outputStore 94 (Encoding.vista.encode (updated round leader degree old messages)) := by
    funext r
    fin_cases r <;> simp [finishedStore,assembled,assembledStore,imported,Receive.messagesResult,
      ready,preparedStore,labelsStore,outputStore,updated,merged,node]
  rw [final] at rf
  refine ⟨_,?_,rp.sequence (rm.sequence (ra.sequence rf))⟩
  have source : ready 70=(Encoding.list Receive.messageCodec).encode messages := by simp [ready,preparedStore]
  rw [source] at bm
  dsimp only [completeBudget]
  dsimp only [merged,node] at ba bf
  omega

theorem updated_eq_rawUpdate (round : Nat) (leader : Bool) (degree : Nat) (old : Executable.Vista)
    (messages : List (Executable.Vista×Nat)) (valid : old.valid=true)
    (roundEq : (old.node old.bottom).level=round) (leaderEq : (old.node old.bottom).leader=leader)
    (messageValid : ∀ message∈messages,message.1.valid=true ∧
      (message.1.node message.1.bottom).level=round) :
    updated round leader degree old messages=Executable.rawUpdate old messages degree := by
  have fresh := Executable.rawUpdate_starting_old_intern old messages degree valid (by
    intro message member
    obtain ⟨good,same⟩ := messageValid message member
    exact ⟨good,same.trans roundEq.symm⟩)
  rw [roundEq,leaderEq] at fresh
  rw [Executable.rawUpdate_starting_old old messages degree valid,roundEq,leaderEq]
  unfold updated internVista newNode
  dsimp only at fresh ⊢
  rw [fresh]

end Counting.StackMachine.DagUpdate.Raw
