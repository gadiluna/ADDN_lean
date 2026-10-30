import Counting.ExecutableRefinementCoreCorrectness
import Counting.ExecutableRefinementPhysical

namespace Counting.Executable
open scoped BigOperators

/-- Direct refinement of the compact physical interface: one binary count
per sender, the real `advanceCore?`, and no expansion into individual packets. -/
theorem binary_core_update_physical {V : Type} [Fintype V]
    (G : Nat → V → V → Nat) (leader : V → Bool) (ell depth : Nat) (positive : 0 < ell)
    (states : V → LocalState)
    (represented : ∀ x, StateRep ell depth (Counting.history G leader depth x) (states x))
    (active : ∀ x, (states x).output = none) (receiver : V) :
    ∃ next, advanceCore? (states receiver)
        (physicalBundles (G (depth + 1)) (fun sender => (states sender).vista) receiver)
        (∑ sender, G (depth + 1) receiver sender) = some next ∧
      StateRep ell (depth + 1) (Counting.history G leader (depth + 1) receiver) next ∧
      next.output = Counting.TimingProtocol.coreDecision ell (depth + 1)
        (Counting.history G leader (depth + 1) receiver) := by
  obtain ⟨vista, updated, vistaValid, level, history⟩ := physical_vista_update G leader depth
    (fun sender => (states sender).vista) (fun sender => (represented sender).valid)
    (fun sender => (represented sender).level) (fun sender => (represented sender).history) receiver
  have output := coreScheduledOutput_history ell vista vistaValid (depth + 1)
    (Counting.history G leader (depth + 1) receiver) level history
  let next : LocalState := { (states receiver) with
    vista := vista
    output := Counting.TimingProtocol.coreDecision ell (depth + 1)
      (Counting.history G leader (depth + 1) receiver) }
  refine ⟨next, ?_, ⟨(represented receiver).leaderCount, vistaValid, level, history⟩, rfl⟩
  rw [advanceCore_active_of_update _ _ _ vista (active receiver)
    (by rw [(represented receiver).leaderCount]; exact positive) updated,
    (represented receiver).leaderCount, output]
  simp only [next, (represented receiver).leaderCount]

noncomputable def binaryCoreNetworkRun {V : Type} [Fintype V]
    (G : Nat → V → V → Nat) (leader : V → Bool) (ell : Nat) : Nat → V → LocalState
  | 0, receiver => initialState ell (leader receiver)
  | depth + 1, receiver =>
      let previous := binaryCoreNetworkRun G leader ell depth
      (advanceCore? (previous receiver) (activePhysicalBundles (G (depth + 1)) previous receiver)
        (∑ sender, G (depth + 1) receiver sender)).getD (previous receiver)

theorem binary_core_network_before {V : Type} [Fintype V]
    (G : Nat → V → V → Nat) (leader : V → Bool) (ell : Nat)
    (network : Counting.Admissible ell G leader) (depth : Nat)
    (before : depth < (2 * Fintype.card V - 1)) (receiver : V) :
    StateRep ell depth (Counting.history G leader depth receiver) (binaryCoreNetworkRun G leader ell depth receiver) ∧
      (binaryCoreNetworkRun G leader ell depth receiver).output = none := by
  induction depth generalizing receiver with
  | zero => exact ⟨initialState_rep ell (leader receiver), rfl⟩
  | succ depth ih =>
      have earlier : depth < (2 * Fintype.card V - 1) := by omega
      have represented := fun sender => (ih earlier sender).1
      have active := fun sender => (ih earlier sender).2
      obtain ⟨next, updated, rep, output⟩ := binary_core_update_physical G leader ell depth network.positive
        (binaryCoreNetworkRun G leader ell depth) represented active receiver
      rw [Counting.TimingProtocol.coreDecision_before G leader ell (depth + 1) receiver network before] at output
      simpa only [binaryCoreNetworkRun, activePhysicalBundles_of_active _ _ active, updated, Option.getD_some]
        using And.intro rep output

theorem binary_core_network_at_stop {V : Type} [Fintype V]
    (G : Nat → V → V → Nat) (leader : V → Bool) (ell : Nat)
    (network : Counting.Admissible ell G leader) (receiver : V) :
    StateRep ell ((2 * Fintype.card V - 1))
        (Counting.history G leader ((2 * Fintype.card V - 1)) receiver)
        (binaryCoreNetworkRun G leader ell ((2 * Fintype.card V - 1)) receiver) ∧
      (binaryCoreNetworkRun G leader ell ((2 * Fintype.card V - 1)) receiver).output =
        some (Fintype.card V) := by
  have population : 0 < Fintype.card V := lt_of_lt_of_le network.positive network.leaderCount_le_card
  have positive : 0 < 2 * Fintype.card V - 1 := by omega
  obtain ⟨depth, stop⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt positive)
  have previous := binary_core_network_before G leader ell network depth (by omega)
  have represented := fun sender => (previous sender).1
  have active := fun sender => (previous sender).2
  obtain ⟨next, updated, rep, output⟩ := binary_core_update_physical G leader ell depth network.positive
    (binaryCoreNetworkRun G leader ell depth) represented active receiver
  have atStop := Counting.TimingProtocol.coreDecision_at G leader ell receiver network
  rw [stop] at atStop
  rw [atStop] at output
  rw [stop]
  simpa only [binaryCoreNetworkRun, activePhysicalBundles_of_active _ _ active, updated, Option.getD_some]
    using And.intro rep output

theorem binary_core_network_frozen {V : Type} [Fintype V]
    (G : Nat → V → V → Nat) (leader : V → Bool) (ell : Nat)
    (network : Counting.Admissible ell G leader) (delay : Nat) (receiver : V) :
    binaryCoreNetworkRun G leader ell ((2 * Fintype.card V - 1) + delay) receiver =
      binaryCoreNetworkRun G leader ell ((2 * Fintype.card V - 1)) receiver := by
  induction delay with
  | zero => rfl
  | succ delay ih =>
      rw [Nat.add_succ, binaryCoreNetworkRun, ih]
      have halted := (binary_core_network_at_stop G leader ell network receiver).2
      rw [advanceCore_halted _ _ _ (by simp [halted]), Option.getD_some]


theorem binary_core_network_step_total {V : Type} [Fintype V]
    (G : Nat → V → V → Nat) (leader : V → Bool) (ell : Nat)
    (network : Counting.Admissible ell G leader) (depth : Nat) (receiver : V) :
    ∃ next, advanceCore? (binaryCoreNetworkRun G leader ell depth receiver)
      (activePhysicalBundles (G (depth + 1)) (binaryCoreNetworkRun G leader ell depth) receiver)
      (∑ sender, G (depth + 1) receiver sender) = some next := by
  by_cases before : depth < (2 * Fintype.card V - 1)
  · have previous := binary_core_network_before G leader ell network depth before
    have active := fun sender => (previous sender).2
    obtain ⟨next, updated, _, _⟩ := binary_core_update_physical G leader ell depth network.positive
      (binaryCoreNetworkRun G leader ell depth) (fun sender => (previous sender).1) active receiver
    exact ⟨next, by simpa only [activePhysicalBundles_of_active _ _ active] using updated⟩
  · obtain ⟨delay, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt before)
    refine ⟨_, advanceCore_halted _ _ _ ?_⟩
    rw [binary_core_network_frozen G leader ell network delay receiver,
      (binary_core_network_at_stop G leader ell network receiver).2]
    rfl

/-- No stopped sender contributes even one binary arc bundle. -/
theorem binary_core_network_silent_after {V : Type} [Fintype V]
    (G : Nat → V → V → Nat) (leader : V → Bool) (ell : Nat)
    (network : Counting.Admissible ell G leader) (delay : Nat) (receiver : V) :
    activePhysicalBundles (G ((2 * Fintype.card V - 1) + delay + 1))
      (binaryCoreNetworkRun G leader ell ((2 * Fintype.card V - 1) + delay)) receiver = [] := by
  have halted : ∀ sender,
      (binaryCoreNetworkRun G leader ell ((2 * Fintype.card V - 1) + delay) sender).output =
        some (Fintype.card V) := by
    intro sender
    rw [binary_core_network_frozen G leader ell network delay sender]
    exact (binary_core_network_at_stop G leader ell network sender).2
  simp only [activePhysicalBundles, halted, Option.isNone_some, List.filter_false, senderBundles, List.filterMap_nil]

end Counting.Executable
