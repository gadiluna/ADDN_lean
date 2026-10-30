import Counting.EncodingNetworkBounds

namespace Counting.Encoding
open Executable
open scoped BigOperators

/-- Explicit finite sums use the input's listed physical agents. -/
theorem finRange_sum {A : Type} [AddCommMonoid A] (n : Nat) (f : Fin n → A) :
    ((List.finRange n).map f).sum = ∑ x, f x := by
  rw [← List.sum_toFinset _ (List.nodup_finRange n)]
  congr 1
  ext x
  simp

/-- Binary bundles assembled with a computable enumeration of the input
population denote exactly the received multiset of physical histories. -/
theorem inputBundles_histories (input : Simulation.Input)
    (edge : InputAgent input → InputAgent input → Nat)
    (states : InputAgent input → Vista) (receiver : InputAgent input) (depth : Nat) :
    receivedHistories depth (senderBundles (List.finRange input.leaders.size) edge states receiver) =
      Counting.incoming edge (fun sender => decodeNode (states sender) depth (states sender).bottom) receiver := by
  rw [senderBundles_histories, finRange_sum]
  rfl

/-- Computable all-active reconstruction from the binary network input.
Only the anonymous updater receives messages; physical indices are used
here solely to execute the listed network. -/
def inputVistaRun (input : Simulation.Input) : Nat → InputAgent input → Vista
  | 0, receiver => initialVista (inputLeader input receiver)
  | depth+1, receiver =>
      let previous := inputVistaRun input depth
      let bundles := senderBundles (List.finRange input.leaders.size)
        (inputGraph input (depth+1)) previous receiver
      let degree := ((List.finRange input.leaders.size).map
        (fun target => inputGraph input (depth+1) receiver target)).sum
      (updateVista? (previous receiver) bundles degree).getD (previous receiver)

/-- Every explicit-network reconstruction step succeeds and has the
correct physical semantics, even before model validation. -/
theorem input_vista_update (input : Simulation.Input) (depth : Nat)
    (states : InputAgent input → Vista)
    (valid : ∀ sender, (states sender).valid = true)
    (levels : ∀ sender, ((states sender).node (states sender).bottom).level = depth)
    (histories : ∀ sender, decodeNode (states sender) depth (states sender).bottom =
      Counting.history (inputGraph input) (inputLeader input) depth sender)
    (receiver : InputAgent input) :
    ∃ next, updateVista? (states receiver)
      (senderBundles (List.finRange input.leaders.size) (inputGraph input (depth+1)) states receiver)
      (((List.finRange input.leaders.size).map
        (fun target => inputGraph input (depth+1) receiver target)).sum) = some next ∧
      next.valid = true ∧ (next.node next.bottom).level = depth+1 ∧
      decodeNode next (depth+1) next.bottom =
        Counting.history (inputGraph input) (inputLeader input) (depth+1) receiver := by
  have messages : ∀ message ∈ senderBundles (List.finRange input.leaders.size)
      (inputGraph input (depth+1)) states receiver,
      message.1.valid = true ∧ 0 < message.2 ∧
        (message.1.node message.1.bottom).level = ((states receiver).node (states receiver).bottom).level := by
    intro message present
    obtain ⟨sender, _, positive, rfl⟩ := mem_senderBundles _ _ _ _ _ present
    exact ⟨valid sender, positive, (levels sender).trans (levels receiver).symm⟩
  obtain ⟨next, updated, nextValid, nextLevel⟩ := updateVista_total (states receiver)
    (senderBundles (List.finRange input.leaders.size) (inputGraph input (depth+1)) states receiver)
    (((List.finRange input.leaders.size).map
      (fun target => inputGraph input (depth+1) receiver target)).sum) (valid receiver) messages
  refine ⟨next, updated, nextValid, nextLevel.trans (congrArg (·+1) (levels receiver)), ?_⟩
  have sound := (updateVista_sound _ _ _ _ updated).2
  have oldLevel := levels receiver
  subst depth
  rw [inputBundles_histories, finRange_sum] at sound
  have messageHistories : (fun sender => decodeNode (states sender)
      ((states receiver).node (states receiver).bottom).level (states sender).bottom) =
      Counting.history (inputGraph input) (inputLeader input)
        ((states receiver).node (states receiver).bottom).level := funext histories
  rw [messageHistories] at sound
  exact sound.trans (Prod.ext (histories receiver) (Prod.ext rfl rfl))

/-- The fallback in `inputVistaRun` is unreachable; the result is a valid
DAG representing the actual history at every finite round. -/
theorem inputVistaRun_correct (input : Simulation.Input) (depth : Nat) (receiver : InputAgent input) :
    (inputVistaRun input depth receiver).valid = true ∧
    ((inputVistaRun input depth receiver).node (inputVistaRun input depth receiver).bottom).level = depth ∧
    decodeNode (inputVistaRun input depth receiver) depth (inputVistaRun input depth receiver).bottom =
      Counting.history (inputGraph input) (inputLeader input) depth receiver := by
  induction depth generalizing receiver with
  | zero => exact ⟨initialVista_valid _, by simp [inputVistaRun, initialVista, Vista.node], rfl⟩
  | succ depth ih =>
      obtain ⟨next, updated, valid, level, history⟩ := input_vista_update input depth
        (inputVistaRun input depth) (fun sender => (ih sender).1)
        (fun sender => (ih sender).2.1) (fun sender => (ih sender).2.2) receiver
      simpa only [inputVistaRun, updated, Option.getD_some] using And.intro valid ⟨level, history⟩

/-- The executable reconstruction stores the whole preceding configuration
once, so physical senders share its already-computed DAGs. -/
def inputVistaArrayRun (input : Simulation.Input) : Nat → Array Vista
  | 0 => Array.ofFn (fun receiver : InputAgent input => initialVista (inputLeader input receiver))
  | depth+1 =>
      let previous := inputVistaArrayRun input depth
      let states := fun sender : InputAgent input =>
        (previous[sender.val]?).getD (initialVista (inputLeader input sender))
      Array.ofFn (fun receiver : InputAgent input =>
        let bundles := senderBundles (List.finRange input.leaders.size)
          (inputGraph input (depth+1)) states receiver
        let degree := ((List.finRange input.leaders.size).map
          (fun target => inputGraph input (depth+1) receiver target)).sum
        (updateVista? (states receiver) bundles degree).getD (states receiver))

theorem inputVistaArrayRun_eq (input : Simulation.Input) (depth : Nat) :
    inputVistaArrayRun input depth = Array.ofFn (inputVistaRun input depth) := by
  induction depth with
  | zero => rfl
  | succ depth ih =>
      simp only [inputVistaArrayRun, ih, Array.getElem?_ofFn, Fin.isLt, dite_true,
        Fin.eta, Option.getD_some]
      rfl

/-- Final DAGs in the same explicit order as the input population. -/
def inputVistas (input : Simulation.Input) : Array Vista :=
  inputVistaArrayRun input input.rounds.size

@[simp] theorem inputVistas_size (input : Simulation.Input) :
    (inputVistas input).size = input.leaders.size := by simp [inputVistas, inputVistaArrayRun_eq]

@[simp] theorem inputVistas_get (input : Simulation.Input) (receiver : InputAgent input) :
    (inputVistas input)[receiver.val]'(by rw [inputVistas_size]; exact receiver.isLt) =
      inputVistaRun input input.rounds.size receiver := by simp [inputVistas, inputVistaArrayRun_eq]

theorem inputVistas_correct (input : Simulation.Input) (receiver : InputAgent input) :
    let v := (inputVistas input)[receiver.val]'(by rw [inputVistas_size]; exact receiver.isLt)
    v.valid = true ∧ (v.node v.bottom).level = input.rounds.size ∧
      decodeNode v input.rounds.size v.bottom = inputHistory input receiver := by
  simp only [inputVistas_get]
  exact inputVistaRun_correct input input.rounds.size receiver

/-- Polynomial binary size for the DAGs produced by the computable input
reconstruction, including all indices, labels and framing bits. -/
theorem inputVistas_encoding_length (input : Simulation.Input) (receiver : InputAgent input) :
    let v := (inputVistas input)[receiver.val]'(by rw [inputVistas_size]; exact receiver.isLt)
    (vista.encode v).length ≤ 200*((networkInput.encode input).length+1)^5 := by
  dsimp only
  let v := (inputVistas input)[receiver.val]'(by rw [inputVistas_size]; exact receiver.isLt)
  obtain ⟨valid, depth, physical⟩ := inputVistas_correct input receiver
  have bound := physical_vista_encoding_length (inputGraph input) (inputLeader input)
    input.rounds.size receiver v valid depth physical
    (input.leaders.size^2 * 2^(networkInput.encode input).length) (inputGraph_mass_bound input)
  dsimp only at bound
  have polynomial := network_vista_polynomial_arithmetic input.leaders.size input.rounds.size
    (Nat.size (input.leaders.size^2 * 2^(networkInput.encode input).length))
    (networkInput.encode input).length (network_agents_le_length input) (network_rounds_le_length input)
    (input_mass_bits_le input)
  exact bound.trans (by simpa only [InputAgent, Fintype.card_fin] using polynomial)

end Counting.Encoding
