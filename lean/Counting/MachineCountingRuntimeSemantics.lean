import Counting.MachineCountingRuntimeRuns

namespace Counting.Machine.CountingRuntime
open Executable StackMachine.ProtocolAdvance
open scoped BigOperators

noncomputable def runState {V : Type} [Fintype V] (core : Bool)
    (G : Nat → V → V → Nat) (leader : V → Bool) (ell : Nat) : Nat → V → LocalState :=
  if core then binaryCoreNetworkRun G leader ell else binaryNetworkRun G leader ell

def stoppingTime (core : Bool) (population leaders : Nat) : Nat :=
  if core then 2*population-1 else Counting.TimingProtocol.optimizedTime population leaders

noncomputable def messagesAt {V : Type} [Fintype V] (core : Bool)
    (G : Nat → V → V → Nat) (leader : V → Bool) (ell depth : Nat) (receiver : V) : List (Vista×Nat) :=
  activePhysicalBundles (G (depth+1)) (runState core G leader ell depth) receiver

noncomputable def roundInput {V : Type} [Fintype V] (core : Bool)
    (G : Nat → V → V → Nat) (leader : V → Bool) (ell depth : Nat) (receiver : V) : List Bool :=
  inputWord (runState core G leader ell depth receiver) (messagesAt core G leader ell depth receiver)
    (∑ sender,G (depth+1) receiver sender)

theorem stoppingTime_le_twice (core : Bool) (population leaders : Nat) :
    stoppingTime core population leaders ≤ 2*population := by
  cases core <;> simp only [stoppingTime,Bool.false_eq_true,if_false,if_true]
  · unfold Counting.TimingProtocol.optimizedTime
    split
    · omega
    · split <;> omega
  · omega

theorem runState_initial {V : Type} [Fintype V] (core : Bool)
    (G : Nat → V → V → Nat) (leader : V → Bool) (ell : Nat) (receiver : V) :
    runState core G leader ell 0 receiver=initialState ell (leader receiver) := by
  cases core <;> rfl

theorem runState_before {V : Type} [Fintype V] (core : Bool)
    (G : Nat → V → V → Nat) (leader : V → Bool) (ell : Nat)
    (network : Counting.Admissible ell G leader) (depth : Nat)
    (before : depth < stoppingTime core (Fintype.card V) ell) (receiver : V) :
    StateRep ell depth (Counting.history G leader depth receiver) (runState core G leader ell depth receiver) ∧
      (runState core G leader ell depth receiver).output=none := by
  cases core with
  | false => exact binary_network_before G leader ell network depth before receiver
  | true => exact binary_core_network_before G leader ell network depth before receiver

theorem runState_next {V : Type} [Fintype V] (core : Bool)
    (G : Nat → V → V → Nat) (leader : V → Bool) (ell : Nat)
    (network : Counting.Admissible ell G leader) (depth : Nat) (receiver : V) :
    (if core then advanceCore? (runState core G leader ell depth receiver)
      (messagesAt core G leader ell depth receiver) (∑ sender,G (depth+1) receiver sender)
     else advance? (runState core G leader ell depth receiver)
      (messagesAt core G leader ell depth receiver) (∑ sender,G (depth+1) receiver sender))=
        some (runState core G leader ell (depth+1) receiver) := by
  cases core with
  | false =>
    obtain ⟨next,updated⟩ := binary_network_step_total G leader ell network depth receiver
    simp [runState,messagesAt,binaryNetworkRun,updated]
  | true =>
    obtain ⟨next,updated⟩ := binary_core_network_step_total G leader ell network depth receiver
    simp [runState,messagesAt,binaryCoreNetworkRun,updated]

theorem live_messages_valid {V : Type} [Fintype V] (core : Bool)
    (G : Nat → V → V → Nat) (leader : V → Bool) (ell : Nat)
    (network : Counting.Admissible ell G leader) (depth : Nat)
    (before : depth < stoppingTime core (Fintype.card V) ell) (receiver : V) :
    ∀ message∈messagesAt core G leader ell depth receiver,
      message.1.valid=true ∧ 0 < message.2 ∧
        (message.1.node message.1.bottom).level=
          ((runState core G leader ell depth receiver).vista.node
            (runState core G leader ell depth receiver).vista.bottom).level := by
  have previous := runState_before core G leader ell network depth before
  have active := fun sender=>(previous sender).2
  unfold messagesAt
  rw [activePhysicalBundles_of_active _ _ active]
  exact physicalBundles_valid (G (depth+1)) (fun sender=>(runState core G leader ell depth sender).vista) depth
    (fun sender=>(previous sender).1.valid) (fun sender=>(previous sender).1.level) receiver

theorem live_input_bound {V : Type} [Fintype V] (core : Bool)
    (G : Nat → V → V → Nat) (leader : V → Bool) (ell M : Nat)
    (network : Counting.Admissible ell G leader) (depth : Nat)
    (before : depth < stoppingTime core (Fintype.card V) ell)
    (mass : ∀ r,0 < r → r ≤ 2*Fintype.card V → arcMass G r ≤ M) (receiver : V) :
    (roundInput core G leader ell depth receiver).length+1 ≤ 4000*(Fintype.card V+M.size+1)^6 := by
  cases core with
  | false => exact binary_network_input_bound G leader ell M network depth before mass receiver
  | true => exact binary_core_network_input_bound G leader ell M network depth before mass receiver

end Counting.Machine.CountingRuntime
