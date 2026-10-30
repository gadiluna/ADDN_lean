import Counting.StackAuditPropagationAnchorStage

namespace Counting.StackMachine.AuditPropagation

theorem scan_potential (anchor start : Nat) (nodes : List Executable.Node) (values : List Nat) (weights : Array Nat) :
    ((Encoding.array Encoding.natural).encode (assignScan anchor start nodes values weights)).length+
      (Encoding.sequence Encoding.natural (remainingValues anchor nodes values)).length ≤
    ((Encoding.array Encoding.natural).encode weights).length+(Encoding.sequence Encoding.natural values).length := by
  induction nodes generalizing start values weights with
  | nil => rfl
  | cons node nodes ih =>
    have first := chosen_potential node anchor weights start values
    have rest := ih (start+1) (chosenValues node anchor values) (chosenWeights node anchor weights start values)
    rw [assignScan_cons]
    change ((Encoding.array Encoding.natural).encode
      (assignScan anchor (start+1) nodes (chosenValues node anchor values) (chosenWeights node anchor weights start values))).length+
      (Encoding.sequence Encoding.natural (remainingValues anchor nodes (chosenValues node anchor values))).length ≤ _
    omega

theorem assigned_encoded_length (vista : Executable.Vista) (anchor : Nat) (values : Array Nat) :
    ((Encoding.array Encoding.natural).encode (assigned vista anchor values)).length ≤
      ((Encoding.array Encoding.natural).encode (Array.replicate vista.nodes.size 0)).length+
        (Encoding.sequence Encoding.natural values.toList).length := by
  have bound := scan_potential anchor 0 vista.nodes.toList values.toList (Array.replicate vista.nodes.size 0)
  rw [assignScan_vista] at bound
  exact Nat.le_trans (Nat.le_add_right _ _) bound

theorem remainingValues_encoded_length (anchor : Nat) (nodes : List Executable.Node) (values : List Nat) :
    (Encoding.sequence Encoding.natural (remainingValues anchor nodes values)).length ≤
      (Encoding.sequence Encoding.natural values).length := by
  induction nodes generalizing values with
  | nil => rfl
  | cons node nodes ih =>
    have rest := ih (chosenValues node anchor values)
    have chosen : (Encoding.sequence Encoding.natural (chosenValues node anchor values)).length ≤
        (Encoding.sequence Encoding.natural values).length := by
      by_cases selected : node.level=anchor
      · cases values <;> simp [chosenValues,selected,availableValues,Encoding.sequence]
      · simp [chosenValues,selected]
    exact rest.trans chosen

end Counting.StackMachine.AuditPropagation
