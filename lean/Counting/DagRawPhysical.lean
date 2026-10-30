import Counting.DagRawValidity
import Counting.EncodingNetworkWitness

namespace Counting.Encoding
open Executable
open scoped BigOperators

/-- A reconstruction step may preserve the import order of signatures.
Its output still denotes the exact anonymous physical history. -/
theorem raw_input_vista_update (input : Simulation.Input) (depth : Nat)
    (states : InputAgent input → Vista)
    (valid : ∀ sender, (states sender).valid = true)
    (levels : ∀ sender, ((states sender).node (states sender).bottom).level = depth)
    (histories : ∀ sender, decodeNode (states sender) depth (states sender).bottom =
      Counting.history (inputGraph input) (inputLeader input) depth sender)
    (receiver : InputAgent input) :
    let next := rawUpdate (states receiver)
      (senderBundles (List.finRange input.leaders.size) (inputGraph input (depth+1)) states receiver)
      (((List.finRange input.leaders.size).map
        (fun target => inputGraph input (depth+1) receiver target)).sum)
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
  have nextValid := rawUpdate_valid (states receiver) _
    (((List.finRange input.leaders.size).map
      (fun target => inputGraph input (depth+1) receiver target)).sum) (valid receiver) messages
  have correct := rawUpdate_correct (states receiver)
    (senderBundles (List.finRange input.leaders.size) (inputGraph input (depth+1)) states receiver)
    (((List.finRange input.leaders.size).map
      (fun target => inputGraph input (depth+1) receiver target)).sum) (valid receiver)
    (fun m hm => ⟨(messages m hm).1, (messages m hm).2.2⟩)
  refine ⟨nextValid, correct.2.2.1.trans (congrArg (·+1) (levels receiver)), ?_⟩
  have sound := correct.2.2.2
  have oldLevel := levels receiver
  subst depth
  rw [inputBundles_histories, finRange_sum] at sound
  have messageHistories : (fun sender => decodeNode (states sender)
      ((states receiver).node (states receiver).bottom).level (states sender).bottom) =
      Counting.history (inputGraph input) (inputLeader input)
        ((states receiver).node (states receiver).bottom).level := funext histories
  rw [messageHistories] at sound
  exact sound.trans (Prod.ext (histories receiver) (Prod.ext rfl rfl))

def rawInputVistaRun (input : Simulation.Input) : Nat → InputAgent input → Vista
  | 0, receiver => initialVista (inputLeader input receiver)
  | depth+1, receiver =>
      let previous := rawInputVistaRun input depth
      rawUpdate (previous receiver)
        (senderBundles (List.finRange input.leaders.size) (inputGraph input (depth+1)) previous receiver)
        (((List.finRange input.leaders.size).map
          (fun target => inputGraph input (depth+1) receiver target)).sum)

theorem rawInputVistaRun_correct (input : Simulation.Input) (depth : Nat) (receiver : InputAgent input) :
    (rawInputVistaRun input depth receiver).valid = true ∧
    ((rawInputVistaRun input depth receiver).node (rawInputVistaRun input depth receiver).bottom).level = depth ∧
    decodeNode (rawInputVistaRun input depth receiver) depth (rawInputVistaRun input depth receiver).bottom =
      Counting.history (inputGraph input) (inputLeader input) depth receiver := by
  induction depth generalizing receiver with
  | zero => exact ⟨initialVista_valid _, by simp [rawInputVistaRun, initialVista, Vista.node], rfl⟩
  | succ depth ih =>
      exact raw_input_vista_update input depth (rawInputVistaRun input depth)
        (fun sender => (ih sender).1) (fun sender => (ih sender).2.1)
        (fun sender => (ih sender).2.2) receiver

/-- Each preceding configuration is stored once as an array. The function
does not recursively re-evaluate individual sender histories. -/
def rawInputVistaArrayRun (input : Simulation.Input) : Nat → Array Vista
  | 0 => Array.ofFn (fun receiver : InputAgent input => initialVista (inputLeader input receiver))
  | depth+1 =>
      let previous := rawInputVistaArrayRun input depth
      let states := fun sender : InputAgent input =>
        (previous[sender.val]?).getD (initialVista (inputLeader input sender))
      Array.ofFn (fun receiver : InputAgent input =>
        rawUpdate (states receiver)
          (senderBundles (List.finRange input.leaders.size) (inputGraph input (depth+1)) states receiver)
          (((List.finRange input.leaders.size).map
            (fun target => inputGraph input (depth+1) receiver target)).sum))

theorem rawInputVistaArrayRun_eq (input : Simulation.Input) (depth : Nat) :
    rawInputVistaArrayRun input depth = Array.ofFn (rawInputVistaRun input depth) := by
  induction depth with
  | zero => rfl
  | succ depth ih =>
      simp only [rawInputVistaArrayRun, ih, Array.getElem?_ofFn, Fin.isLt, dite_true,
        Fin.eta, Option.getD_some]
      rfl

def rawInputVistas (input : Simulation.Input) : Array Vista :=
  rawInputVistaArrayRun input input.rounds.size

@[simp] theorem rawInputVistas_size (input : Simulation.Input) :
    (rawInputVistas input).size = input.leaders.size := by simp [rawInputVistas, rawInputVistaArrayRun_eq]

@[simp] theorem rawInputVistas_get (input : Simulation.Input) (receiver : InputAgent input) :
    (rawInputVistas input)[receiver.val]'(by rw [rawInputVistas_size]; exact receiver.isLt) =
      rawInputVistaRun input input.rounds.size receiver := by simp [rawInputVistas, rawInputVistaArrayRun_eq]

theorem rawInputVistas_correct (input : Simulation.Input) (receiver : InputAgent input) :
    let v := (rawInputVistas input)[receiver.val]'(by rw [rawInputVistas_size]; exact receiver.isLt)
    v.valid = true ∧ (v.node v.bottom).level = input.rounds.size ∧
      decodeNode v input.rounds.size v.bottom = inputHistory input receiver := by
  simp only [rawInputVistas_get]
  exact rawInputVistaRun_correct input input.rounds.size receiver

/-- A common polynomial bound applies at every listed prefix, although the
serialized DAG need not use canonical node order. -/
theorem rawInputVistaRun_encoding_length (input : Simulation.Input) (depth : Nat)
    (within : depth ≤ input.rounds.size) (receiver : InputAgent input) :
    (vista.encode (rawInputVistaRun input depth receiver)).length ≤
      200*((networkInput.encode input).length+1)^5 := by
  obtain ⟨valid, level, physical⟩ := rawInputVistaRun_correct input depth receiver
  have bound := physical_vista_encoding_length (inputGraph input) (inputLeader input)
    depth receiver (rawInputVistaRun input depth receiver) valid level physical
    (input.leaders.size^2 * 2^(networkInput.encode input).length)
    (fun r positive before => inputGraph_mass_bound input r positive (before.trans within))
  have polynomial := network_vista_polynomial_arithmetic input.leaders.size depth
    (Nat.size (input.leaders.size^2 * 2^(networkInput.encode input).length))
    (networkInput.encode input).length (network_agents_le_length input)
    (within.trans (network_rounds_le_length input)) (input_mass_bits_le input)
  exact bound.trans (by simpa only [InputAgent, Fintype.card_fin] using polynomial)

theorem rawInputVistas_encoding_length (input : Simulation.Input) (receiver : InputAgent input) :
    let v := (rawInputVistas input)[receiver.val]'(by rw [rawInputVistas_size]; exact receiver.isLt)
    (vista.encode v).length ≤ 200*((networkInput.encode input).length+1)^5 := by
  simp only [rawInputVistas_get]
  exact rawInputVistaRun_encoding_length input _ le_rfl receiver

def rawAgentVista (input : Simulation.Input) (agent : InputAgent input) : Vista :=
  (rawInputVistas input)[agent.val]'(by rw [rawInputVistas_size]; exact agent.isLt)

theorem rawAgentVista_atMostOne_iff (input : Simulation.Input) (agent : InputAgent input) :
    Realizability.AtMostOneVista (inputLeaderCount input) (rawAgentVista input agent).denotes ↔
      Realizability.AtMostOneVista (inputLeaderCount input) (inputHistory input agent) := by
  obtain ⟨_, depth, history⟩ := rawInputVistas_correct input agent
  exact atMostOne_decode_iff _ _ _ _ depth history

theorem rawAgentVista_input_length (input : Simulation.Input) (agent : InputAgent input) :
    (vistaInput.encode (rawAgentVista input agent, inputLeaderCount input)).length ≤
      203*((networkInput.encode input).length+1)^5 := by
  have dag := rawInputVistas_encoding_length input agent
  have leaders := inputLeaderCount_bits_le_length input
  have power : (networkInput.encode input).length+1 ≤
      ((networkInput.encode input).length+1)^5 := Nat.le_pow (by norm_num)
  rw [vistaInput_length]
  dsimp only [rawAgentVista]
  nlinarith

end Counting.Encoding
