import Counting.DagSemanticsValidityIteration
import Counting.DagSemanticsAncestors

namespace Counting.Executable
open scoped BigOperators

/-- Global proof harness only: each sender contributes one binary arc bundle.
The updater itself still receives only vistas, multiplicities, and outdegree. -/
def senderBundles {V : Type} (senders : List V) (edge : V → V → Nat)
    (states : V → Vista) (receiver : V) : List (Vista × Nat) :=
  senders.filterMap (fun sender =>
    if edge sender receiver = 0 then none else some (states sender, edge sender receiver))

noncomputable def physicalBundles {V : Type} [Fintype V] (edge : V → V → Nat)
    (states : V → Vista) (receiver : V) : List (Vista × Nat) :=
  senderBundles Finset.univ.toList edge states receiver

theorem mem_senderBundles {V : Type} (senders : List V) (edge : V → V → Nat)
    (states : V → Vista) (receiver : V) (message : Vista × Nat)
    (present : message ∈ senderBundles senders edge states receiver) :
    ∃ sender ∈ senders, 0 < edge sender receiver ∧ message = (states sender, edge sender receiver) := by
  obtain ⟨sender, member, outcome⟩ := List.mem_filterMap.mp present
  by_cases zero : edge sender receiver = 0
  · simp [zero] at outcome
  · refine ⟨sender, member, Nat.pos_of_ne_zero zero, ?_⟩
    simpa only [zero, if_false, Option.some.injEq] using outcome.symm

theorem senderBundles_histories {V : Type} (senders : List V) (edge : V → V → Nat)
    (states : V → Vista) (receiver : V) (depth : Nat) :
    receivedHistories depth (senderBundles senders edge states receiver) =
      (senders.map (fun sender => Multiset.replicate (edge sender receiver)
        (decodeNode (states sender) depth (states sender).bottom))).sum := by
  induction senders with
  | nil => rfl
  | cons sender rest ih =>
      by_cases zero : edge sender receiver = 0
      · simpa [senderBundles, receivedHistories, zero] using ih
      · simpa [senderBundles, receivedHistories, zero] using congrArg
          (fun tail => Multiset.replicate (edge sender receiver)
            (decodeNode (states sender) depth (states sender).bottom) + tail) ih

theorem physicalBundles_histories {V : Type} [Fintype V] (edge : V → V → Nat)
    (states : V → Vista) (receiver : V) (depth : Nat) :
    receivedHistories depth (physicalBundles edge states receiver) =
      Counting.incoming edge (fun sender => decodeNode (states sender) depth (states sender).bottom) receiver := by
  classical
  rw [physicalBundles, senderBundles_histories]
  rw [← List.sum_toFinset _ (Finset.nodup_toList (Finset.univ : Finset V)), Finset.toList_toFinset]
  rfl

theorem physicalBundles_valid {V : Type} [Fintype V] (edge : V → V → Nat)
    (states : V → Vista) (depth : Nat)
    (valid : ∀ sender, (states sender).valid = true)
    (levels : ∀ sender, ((states sender).node (states sender).bottom).level = depth) (receiver : V) :
    ∀ message ∈ physicalBundles edge states receiver,
      message.1.valid = true ∧ 0 < message.2 ∧
        (message.1.node message.1.bottom).level = ((states receiver).node (states receiver).bottom).level := by
  intro message present
  obtain ⟨sender, _, positive, rfl⟩ := mem_senderBundles _ _ _ _ _ present
  exact ⟨valid sender, positive, (levels sender).trans (levels receiver).symm⟩

/-- One actual synchronous round of the executable updater reconstructs the
physical full-information history. No connectivity assumption is required. -/
theorem physical_vista_update {V : Type} [Fintype V]
    (G : Nat → V → V → Nat) (leader : V → Bool) (depth : Nat) (states : V → Vista)
    (valid : ∀ sender, (states sender).valid = true)
    (levels : ∀ sender, ((states sender).node (states sender).bottom).level = depth)
    (histories : ∀ sender, decodeNode (states sender) depth (states sender).bottom =
      Counting.history G leader depth sender) (receiver : V) :
    ∃ next, updateVista? (states receiver) (physicalBundles (G (depth + 1)) states receiver)
        (∑ sender, G (depth + 1) receiver sender) = some next ∧ next.valid = true ∧
      (next.node next.bottom).level = depth + 1 ∧
      decodeNode next (depth + 1) next.bottom = Counting.history G leader (depth + 1) receiver := by
  have messages := physicalBundles_valid (G (depth + 1)) states depth valid levels receiver
  obtain ⟨next, updated, nextValid, nextLevel⟩ := updateVista_total (states receiver)
    (physicalBundles (G (depth + 1)) states receiver) (∑ sender, G (depth + 1) receiver sender)
    (valid receiver) messages
  refine ⟨next, updated, nextValid, nextLevel.trans (congrArg (fun t => t + 1) (levels receiver)), ?_⟩
  have sound := (updateVista_sound _ _ _ _ updated).2
  have oldLevel := levels receiver
  subst depth
  rw [physicalBundles_histories] at sound
  have messageHistories : (fun sender => decodeNode (states sender)
      ((states receiver).node (states receiver).bottom).level (states sender).bottom) =
      Counting.history G leader ((states receiver).node (states receiver).bottom).level := funext histories
  rw [messageHistories] at sound
  exact sound.trans (Prod.ext (histories receiver) (Prod.ext rfl rfl))

/-- An always-active run of the real updater, used solely as a global model.
The fallback branch is proved unreachable by `physical_vista_run_correct`. -/
noncomputable def physicalVistaRun {V : Type} [Fintype V]
    (G : Nat → V → V → Nat) (leader : V → Bool) : Nat → V → Vista
  | 0, receiver => initialVista (leader receiver)
  | depth + 1, receiver =>
      let previous := physicalVistaRun G leader depth
      (updateVista? (previous receiver) (physicalBundles (G (depth + 1)) previous receiver)
        (∑ sender, G (depth + 1) receiver sender)).getD (previous receiver)

/-- From the real initial DAG, every all-active physical prefix is valid,
has the correct round number, and decodes to its physical history. -/
theorem physical_vista_run_correct {V : Type} [Fintype V]
    (G : Nat → V → V → Nat) (leader : V → Bool) (depth : Nat) (receiver : V) :
    (physicalVistaRun G leader depth receiver).valid = true ∧
    ((physicalVistaRun G leader depth receiver).node (physicalVistaRun G leader depth receiver).bottom).level = depth ∧
    decodeNode (physicalVistaRun G leader depth receiver) depth
      (physicalVistaRun G leader depth receiver).bottom = Counting.history G leader depth receiver := by
  induction depth generalizing receiver with
  | zero =>
      exact ⟨initialVista_valid (leader receiver), by simp [physicalVistaRun, initialVista, Vista.node], rfl⟩
  | succ depth ih =>
      have all : ∀ sender,
          (physicalVistaRun G leader depth sender).valid = true ∧
          ((physicalVistaRun G leader depth sender).node (physicalVistaRun G leader depth sender).bottom).level = depth ∧
          decodeNode (physicalVistaRun G leader depth sender) depth
            (physicalVistaRun G leader depth sender).bottom = Counting.history G leader depth sender := by
        intro sender
        exact ih sender
      obtain ⟨next, updated, valid, level, history⟩ := physical_vista_update G leader depth
        (physicalVistaRun G leader depth) (fun sender => (all sender).1)
        (fun sender => (all sender).2.1) (fun sender => (all sender).2.2) receiver
      simpa only [physicalVistaRun, updated, Option.getD_some] using And.intro valid ⟨level, history⟩

end Counting.Executable
