import Counting.ExecutableRefinementCorrectness

namespace Counting.Executable
open scoped BigOperators

/-- Direct refinement of the compact physical interface: one binary count
per sender, the real `advance?`, and no expansion into individual packets. -/
theorem binary_update_physical {V : Type} [Fintype V]
    (G : Nat → V → V → Nat) (leader : V → Bool) (ell depth : Nat) (positive : 0 < ell)
    (states : V → LocalState)
    (represented : ∀ x, StateRep ell depth (Counting.history G leader depth x) (states x))
    (active : ∀ x, (states x).output = none) (receiver : V) :
    ∃ next, advance? (states receiver)
        (physicalBundles (G (depth + 1)) (fun sender => (states sender).vista) receiver)
        (∑ sender, G (depth + 1) receiver sender) = some next ∧
      StateRep ell (depth + 1) (Counting.history G leader (depth + 1) receiver) next ∧
      next.output = Counting.TimingProtocol.optimizedDecision ell (depth + 1)
        (Counting.history G leader (depth + 1) receiver) := by
  obtain ⟨vista, updated, vistaValid, level, history⟩ := physical_vista_update G leader depth
    (fun sender => (states sender).vista) (fun sender => (represented sender).valid)
    (fun sender => (represented sender).level) (fun sender => (represented sender).history) receiver
  have output := scheduledOutput_history ell positive vista vistaValid (depth + 1)
    (Counting.history G leader (depth + 1) receiver) level history
  let next : LocalState := { (states receiver) with
    vista := vista
    output := Counting.TimingProtocol.optimizedDecision ell (depth + 1)
      (Counting.history G leader (depth + 1) receiver) }
  refine ⟨next, ?_, ⟨(represented receiver).leaderCount, vistaValid, level, history⟩, rfl⟩
  rw [advance_active_of_update _ _ _ vista (active receiver)
    (by rw [(represented receiver).leaderCount]; exact positive) updated,
    (represented receiver).leaderCount, output]
  simp only [next, (represented receiver).leaderCount]

/-- The global harness omits halted senders and retains binary arc counts.
Agent identities occur only in this simulation of the physical network. -/
noncomputable def activePhysicalBundles {V : Type} [Fintype V] (edge : V → V → Nat)
    (states : V → LocalState) (receiver : V) : List (Vista × Nat) :=
  senderBundles (Finset.univ.toList.filter (fun sender => (states sender).output.isNone))
    edge (fun sender => (states sender).vista) receiver

theorem activePhysicalBundles_of_active {V : Type} [Fintype V] (edge : V → V → Nat)
    (states : V → LocalState) (active : ∀ sender, (states sender).output = none) (receiver : V) :
    activePhysicalBundles edge states receiver = physicalBundles edge (fun sender => (states sender).vista) receiver := by
  simp [activePhysicalBundles, physicalBundles, active]

noncomputable def binaryNetworkRun {V : Type} [Fintype V]
    (G : Nat → V → V → Nat) (leader : V → Bool) (ell : Nat) : Nat → V → LocalState
  | 0, receiver => initialState ell (leader receiver)
  | depth + 1, receiver =>
      let previous := binaryNetworkRun G leader ell depth
      (advance? (previous receiver) (activePhysicalBundles (G (depth + 1)) previous receiver)
        (∑ sender, G (depth + 1) receiver sender)).getD (previous receiver)

theorem binary_network_before {V : Type} [Fintype V]
    (G : Nat → V → V → Nat) (leader : V → Bool) (ell : Nat)
    (network : Counting.Admissible ell G leader) (depth : Nat)
    (before : depth < Counting.TimingProtocol.optimizedTime (Fintype.card V) ell) (receiver : V) :
    StateRep ell depth (Counting.history G leader depth receiver) (binaryNetworkRun G leader ell depth receiver) ∧
      (binaryNetworkRun G leader ell depth receiver).output = none := by
  induction depth generalizing receiver with
  | zero => exact ⟨initialState_rep ell (leader receiver), rfl⟩
  | succ depth ih =>
      have earlier : depth < Counting.TimingProtocol.optimizedTime (Fintype.card V) ell := by omega
      have represented := fun sender => (ih earlier sender).1
      have active := fun sender => (ih earlier sender).2
      obtain ⟨next, updated, rep, output⟩ := binary_update_physical G leader ell depth network.positive
        (binaryNetworkRun G leader ell depth) represented active receiver
      rw [Counting.TimingProtocol.optimizedDecision_before G leader ell (depth + 1) receiver network before] at output
      simpa only [binaryNetworkRun, activePhysicalBundles_of_active _ _ active, updated, Option.getD_some]
        using And.intro rep output

theorem binary_network_at_stop {V : Type} [Fintype V]
    (G : Nat → V → V → Nat) (leader : V → Bool) (ell : Nat)
    (network : Counting.Admissible ell G leader) (receiver : V) :
    StateRep ell (Counting.TimingProtocol.optimizedTime (Fintype.card V) ell)
        (Counting.history G leader (Counting.TimingProtocol.optimizedTime (Fintype.card V) ell) receiver)
        (binaryNetworkRun G leader ell (Counting.TimingProtocol.optimizedTime (Fintype.card V) ell) receiver) ∧
      (binaryNetworkRun G leader ell (Counting.TimingProtocol.optimizedTime (Fintype.card V) ell) receiver).output =
        some (Fintype.card V) := by
  have positive := Counting.TimingProtocol.optimizedTime_positive G leader ell network
  obtain ⟨depth, stop⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt positive)
  have previous := binary_network_before G leader ell network depth (by omega)
  have represented := fun sender => (previous sender).1
  have active := fun sender => (previous sender).2
  obtain ⟨next, updated, rep, output⟩ := binary_update_physical G leader ell depth network.positive
    (binaryNetworkRun G leader ell depth) represented active receiver
  have atStop := Counting.TimingProtocol.optimizedDecision_at G leader ell receiver network
  rw [stop] at atStop
  rw [atStop] at output
  rw [stop]
  simpa only [binaryNetworkRun, activePhysicalBundles_of_active _ _ active, updated, Option.getD_some]
    using And.intro rep output

theorem binary_network_frozen {V : Type} [Fintype V]
    (G : Nat → V → V → Nat) (leader : V → Bool) (ell : Nat)
    (network : Counting.Admissible ell G leader) (delay : Nat) (receiver : V) :
    binaryNetworkRun G leader ell (Counting.TimingProtocol.optimizedTime (Fintype.card V) ell + delay) receiver =
      binaryNetworkRun G leader ell (Counting.TimingProtocol.optimizedTime (Fintype.card V) ell) receiver := by
  induction delay with
  | zero => rfl
  | succ delay ih =>
      rw [Nat.add_succ, binaryNetworkRun, ih]
      have halted := (binary_network_at_stop G leader ell network receiver).2
      rw [advance_halted _ _ _ (by simp [halted]), Option.getD_some]


theorem binary_network_step_total {V : Type} [Fintype V]
    (G : Nat → V → V → Nat) (leader : V → Bool) (ell : Nat)
    (network : Counting.Admissible ell G leader) (depth : Nat) (receiver : V) :
    ∃ next, advance? (binaryNetworkRun G leader ell depth receiver)
      (activePhysicalBundles (G (depth + 1)) (binaryNetworkRun G leader ell depth) receiver)
      (∑ sender, G (depth + 1) receiver sender) = some next := by
  by_cases before : depth < Counting.TimingProtocol.optimizedTime (Fintype.card V) ell
  · have previous := binary_network_before G leader ell network depth before
    have active := fun sender => (previous sender).2
    obtain ⟨next, updated, _, _⟩ := binary_update_physical G leader ell depth network.positive
      (binaryNetworkRun G leader ell depth) (fun sender => (previous sender).1) active receiver
    exact ⟨next, by simpa only [activePhysicalBundles_of_active _ _ active] using updated⟩
  · obtain ⟨delay, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt before)
    refine ⟨_, advance_halted _ _ _ ?_⟩
    rw [binary_network_frozen G leader ell network delay receiver,
      (binary_network_at_stop G leader ell network receiver).2]
    rfl

/-- No stopped sender contributes even one binary arc bundle. -/
theorem binary_network_silent_after {V : Type} [Fintype V]
    (G : Nat → V → V → Nat) (leader : V → Bool) (ell : Nat)
    (network : Counting.Admissible ell G leader) (delay : Nat) (receiver : V) :
    activePhysicalBundles (G (Counting.TimingProtocol.optimizedTime (Fintype.card V) ell + delay + 1))
      (binaryNetworkRun G leader ell (Counting.TimingProtocol.optimizedTime (Fintype.card V) ell + delay)) receiver = [] := by
  have halted : ∀ sender,
      (binaryNetworkRun G leader ell (Counting.TimingProtocol.optimizedTime (Fintype.card V) ell + delay) sender).output =
        some (Fintype.card V) := by
    intro sender
    rw [binary_network_frozen G leader ell network delay sender]
    exact (binary_network_at_stop G leader ell network sender).2
  simp only [activePhysicalBundles, halted, Option.isNone_some, List.filter_false, senderBundles, List.filterMap_nil]

end Counting.Executable
