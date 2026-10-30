import Counting.InputProtocol
import Counting.DagSemanticsPhysical
import Mathlib.Logic.Encodable.Basic

/-!
# A compact DAG channel for input-labelled histories

An input is stored as metadata in the degree field of a virtual initial layer.
This layer is local initialization, not a physical network round. Every actual
network round thereafter uses the already verified DAG updater, with binary
multiplicities and the actual outdegree. Its interned nodes share common history
subgraphs; no expanded history is stored in the executable channel state.

Semantic expansion and input decoding occur only in the specification below.
This module does not assert that a reconstruction procedure on expanded semantic
histories has an implementation operating directly on DAG indices.
-/

namespace Counting.InputMultiset.Dag

open scoped BigOperators
open Counting.Executable

variable {Input : Type}

/-- Store initial input metadata in one virtual layer before the real rounds. -/
def embed (encode : Input → Nat) :
    (t : Nat) → InputProtocol.FullHistory Input t → Counting.FullHistory (t + 1)
  | 0, h => (h.1, encode h.2, 0)
  | t + 1, h => (embed encode t h.1, h.2.1, h.2.2.map (embed encode t))

/-- Semantic inverse. Invalid metadata may use any total decoder convention. -/
def decode (inputOf : Nat → Input) :
    (t : Nat) → Counting.FullHistory (t + 1) → InputProtocol.FullHistory Input t
  | 0, h => (h.1, inputOf h.2.1)
  | t + 1, h => (decode inputOf t h.1, h.2.1, h.2.2.map (decode inputOf t))

@[simp] theorem decode_embed (encode : Input → Nat) (inputOf : Nat → Input)
    (inverse : Function.LeftInverse inputOf encode) (t : Nat)
    (h : InputProtocol.FullHistory Input t) :
    decode inputOf t (embed encode t h) = h := by
  induction t with
  | zero => exact Prod.ext rfl (inverse h.2)
  | succ t ih =>
      simp only [decode, embed, ih, Multiset.map_map]
      have idfn : (decode inputOf t) ∘ (embed encode t) = id := funext ih
      rw [idfn, Multiset.map_id]
      rcases h with ⟨parent, degree, incoming⟩
      rfl

theorem embed_injective (encode : Input → Nat) (inputOf : Nat → Input)
    (inverse : Function.LeftInverse inputOf encode) (t : Nat) :
    Function.Injective (embed encode t) :=
  Function.LeftInverse.injective (decode_embed encode inputOf inverse t)

/-- Every encodable input type has the required total inverse after choosing a
default only for malformed encodings. Valid input encodings never use it. -/
def encodableInputOf [Encodable Input] [Inhabited Input] (code : Nat) : Input :=
  (Encodable.decode code).getD default

@[simp] theorem encodableInputOf_encode [Encodable Input] [Inhabited Input] (input : Input) :
    encodableInputOf (Encodable.encode input) = input := by
  simp [encodableInputOf]

/-- The executable initial DAG: a virtual metadata step with no messages. -/
def initial (encode : Input → Nat) (leader : Bool) (input : Input) : Vista :=
  (updateVista? (initialVista leader) [] (encode input)).getD (initialVista leader)

/-- Representation relates the compact state to an enriched physical history. -/
structure Rep (encode : Input → Nat) (t : Nat)
    (h : InputProtocol.FullHistory Input t) (vista : Vista) : Prop where
  valid : vista.valid = true
  level : (vista.node vista.bottom).level = t + 1
  history : decodeNode vista (t + 1) vista.bottom = embed encode t h

theorem initial_rep (encode : Input → Nat) (leader : Bool) (input : Input) :
    Rep encode 0 (leader, input) (initial encode leader input) := by
  obtain ⟨next, success, valid, level⟩ := updateVista_total
    (initialVista leader) [] (encode input) (initialVista_valid leader)
    (by intro message present; simp at present)
  have hist := (updateVista_sound _ _ _ _ success).2
  change (next.node next.bottom).level = 1 at level
  change decodeNode next 1 next.bottom = (leader, encode input, 0) at hist
  simp only [initial, success, Option.getD_some]
  exact ⟨valid, level, hist⟩

/-- Reindex the existing updater theorem without introducing dependent casts. -/
theorem update_history_at (old : Vista) (received : List (Vista × Nat))
    (degree : Nat) (next : Vista) (success : updateVista? old received degree = some next)
    (depth : Nat) (level : (old.node old.bottom).level = depth) :
    decodeNode next (depth + 1) next.bottom =
      (decodeNode old depth old.bottom, degree, receivedHistories depth received) := by
  subst depth
  exact (updateVista_sound old received degree next success).2

/-- Decode a compact state in the proof layer. The representation implies exact
recovery of the input-labelled history, not just a Counting projection. -/
theorem Rep.decode_eq {encode : Input → Nat} {t : Nat}
    {h : InputProtocol.FullHistory Input t} {vista : Vista}
    (represented : Rep encode t h vista) (inputOf : Nat → Input)
    (inverse : Function.LeftInverse inputOf encode) :
    decode inputOf t (decodeNode vista (t + 1) vista.bottom) = h := by
  rw [represented.history, decode_embed encode inputOf inverse]

/-- Generic local update refinement. The executable interface consists solely of
the old compact DAG, binary message bundles, and this round's outdegree. -/
theorem update_sound (encode : Input → Nat) (inputOf : Nat → Input)
    (inverse : Function.LeftInverse inputOf encode) (t : Nat)
    (old : Vista) (h : InputProtocol.FullHistory Input t)
    (received : List (Vista × Nat)) (degree : Nat)
    (represented : Rep encode t h old)
    (validMessages : ∀ message ∈ received, message.1.valid = true ∧ 0 < message.2 ∧
      (message.1.node message.1.bottom).level = t + 1) :
    ∃ next, updateVista? old received degree = some next ∧ next.valid = true ∧
      (next.node next.bottom).level = t + 2 ∧
      decode inputOf (t + 1) (decodeNode next (t + 2) next.bottom) =
        (h, degree, (receivedHistories (t + 1) received).map (decode inputOf t)) := by
  obtain ⟨next, success, valid, level⟩ := updateVista_total old received degree represented.valid
    (by
      intro message present
      obtain ⟨hv, hp, hl⟩ := validMessages message present
      exact ⟨hv, hp, hl.trans represented.level.symm⟩)
  have hd := represented.level
  have decodedOwn : decode inputOf t (decodeNode old (t + 1) old.bottom) = h :=
    represented.decode_eq inputOf inverse
  have result := update_history_at old received degree next success (t + 1) hd
  refine ⟨next, success, valid, by simpa only [hd, Nat.add_assoc] using level, ?_⟩
  rw [result]
  exact Prod.ext decodedOwn (Prod.ext rfl rfl)

variable {V : Type} [Fintype V]

/-- One actual network round refines enriched histories. Identifiers occur only
in this global statement, never in the executable updater. -/
theorem physical_update (encode : Input → Nat) (G : Nat → V → V → Nat)
    (leader : V → Bool) (input : V → Input) (t : Nat) (states : V → Vista)
    (represented : ∀ sender,
      Rep encode t (InputProtocol.history G leader input t sender) (states sender)) (receiver : V) :
    ∃ next, updateVista? (states receiver)
        (physicalBundles (G (t + 1)) states receiver)
        (∑ sender, G (t + 1) receiver sender) = some next ∧
      Rep encode (t + 1) (InputProtocol.history G leader input (t + 1) receiver) next := by
  have messages := physicalBundles_valid (G (t + 1)) states (t + 1)
    (fun sender => (represented sender).valid) (fun sender => (represented sender).level) receiver
  obtain ⟨next, success, valid, level⟩ := updateVista_total (states receiver)
    (physicalBundles (G (t + 1)) states receiver) (∑ sender, G (t + 1) receiver sender)
    (represented receiver).valid messages
  have levelOld := (represented receiver).level
  have hs : (fun sender => decodeNode (states sender) (t + 1) (states sender).bottom) =
      fun sender => embed encode t (InputProtocol.history G leader input t sender) := by
    funext sender
    exact (represented sender).history
  refine ⟨next, success, ⟨valid, by simpa only [levelOld] using level, ?_⟩⟩
  have result := update_history_at (states receiver)
    (physicalBundles (G (t + 1)) states receiver) _ next success (t + 1) levelOld
  rw [result, physicalBundles_histories, hs, ← Counting.incoming_map]
  rw [(represented receiver).history]
  rfl

/-- Global always-active harness. Its stored state is just the existing compact
DAG, and each network edge multiplicity remains one binary natural count. -/
noncomputable def physicalRun (encode : Input → Nat) (G : Nat → V → V → Nat)
    (leader : V → Bool) (input : V → Input) : Nat → V → Vista
  | 0, receiver => initial encode (leader receiver) (input receiver)
  | t + 1, receiver =>
      let previous := physicalRun encode G leader input t
      (updateVista? (previous receiver) (physicalBundles (G (t + 1)) previous receiver)
        (∑ sender, G (t + 1) receiver sender)).getD (previous receiver)

theorem physicalRun_rep (encode : Input → Nat) (G : Nat → V → V → Nat)
    (leader : V → Bool) (input : V → Input) (t : Nat) (receiver : V) :
    Rep encode t (InputProtocol.history G leader input t receiver)
      (physicalRun encode G leader input t receiver) := by
  induction t generalizing receiver with
  | zero => exact initial_rep encode (leader receiver) (input receiver)
  | succ t ih =>
      obtain ⟨next, success, represented⟩ := physical_update encode G leader input t
        (physicalRun encode G leader input t) ih receiver
      simpa only [physicalRun, success, Option.getD_some] using represented

theorem physicalRun_step_total (encode : Input → Nat) (G : Nat → V → V → Nat)
    (leader : V → Bool) (input : V → Input) (t : Nat) (receiver : V) :
    ∃ next, updateVista? (physicalRun encode G leader input t receiver)
      (physicalBundles (G (t + 1)) (physicalRun encode G leader input t) receiver)
      (∑ sender, G (t + 1) receiver sender) = some next := by
  obtain ⟨next, success, _⟩ := physical_update encode G leader input t
    (physicalRun encode G leader input t) (physicalRun_rep encode G leader input t) receiver
  exact ⟨next, success⟩

end Counting.InputMultiset.Dag
