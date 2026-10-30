import Counting.DagSemanticsValidity

namespace Counting.Executable

/-- A round supplies only previous vistas with binary multiplicities and the
newly learned outdegree. This wrapper repeatedly invokes the existing updater. -/
abbrev VistaRoundInput := List (Vista × Nat) × Nat

def updateMany? (old : Vista) : List VistaRoundInput → Option Vista
  | [] => some old
  | input :: rest => (updateVista? old input.1 input.2).bind (fun next => updateMany? next rest)

/-- Well-formed external messages at each consecutive round. -/
def InputsAt : Nat → List VistaRoundInput → Prop
  | _, [] => True
  | depth, input :: rest =>
      (∀ message ∈ input.1, message.1.valid = true ∧ 0 < message.2 ∧
        (message.1.node message.1.bottom).level = depth) ∧ InputsAt (depth+1) rest

/-- Every successful finite sequence preserves validity, independently of the
number of updates and without re-assuming validity of intermediate results. -/
theorem updateMany_valid (old : Vista) (inputs : List VistaRoundInput) (next : Vista)
    (valid : old.valid = true) (success : updateMany? old inputs = some next) : next.valid = true := by
  induction inputs generalizing old with
  | nil =>
      have equal : old = next := Option.some.inj success
      exact equal ▸ valid
  | cons input rest ih =>
      cases step : updateVista? old input.1 input.2 with
      | none => simp only [updateMany?, step, Option.bind_none] at success; contradiction
      | some middle =>
          have remainder : updateMany? middle rest = some next := by
            simpa only [updateMany?, step, Option.bind_some] using success
          exact ih middle (updateVista_valid old input.1 input.2 middle step) remainder

/-- Repeated valid inputs of the prescribed consecutive depths never fail. -/
theorem updateMany_total (old : Vista) (inputs : List VistaRoundInput)
    (valid : old.valid = true) (messages : InputsAt (old.node old.bottom).level inputs) :
    ∃ next, updateMany? old inputs = some next ∧ next.valid = true ∧
      (next.node next.bottom).level = (old.node old.bottom).level + inputs.length := by
  induction inputs generalizing old with
  | nil => exact ⟨old, rfl, valid, by simp⟩
  | cons input rest ih =>
      obtain ⟨head, tail⟩ := messages
      obtain ⟨middle, step, middleValid, level⟩ := updateVista_total old input.1 input.2 valid head
      have tailAt : InputsAt (middle.node middle.bottom).level rest := by rw [level]; exact tail
      obtain ⟨next, restSuccess, nextValid, nextLevel⟩ := ih middle middleValid tailAt
      refine ⟨next, ?_, nextValid, ?_⟩
      · simpa only [updateMany?, step, Option.bind_some] using restSuccess
      · simpa only [level, List.length_cons, Nat.add_assoc, Nat.add_comm 1] using nextLevel

/-- In particular, every finite run from an initial input has a valid result
at exactly the number of supplied rounds, including the empty run. -/
theorem initial_updateMany_total (leader : Bool) (inputs : List VistaRoundInput)
    (messages : InputsAt 0 inputs) :
    ∃ next, updateMany? (initialVista leader) inputs = some next ∧ next.valid = true ∧
      (next.node next.bottom).level = inputs.length := by
  have initialLevel : ((initialVista leader).node (initialVista leader).bottom).level = 0 := by
    simp [initialVista, Vista.node]
  have result := updateMany_total (initialVista leader) inputs (initialVista_valid leader)
    (by simpa only [initialLevel] using messages)
  simpa only [initialLevel, Nat.zero_add] using result

end Counting.Executable
