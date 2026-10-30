import Counting.StackAuditPropagationAnchorItem
import Counting.AuditPropagationOrder
import Counting.EncodingArrayUpdateBounds

namespace Counting.StackMachine.AuditPropagation

/-- Weight storage gained by assigning one value is paid for by the
encoded value removed from the input stream. -/
theorem chosen_potential (node : Executable.Node) (anchor : Nat) (weights : Array Nat)
    (index : Nat) (values : List Nat) :
    ((Encoding.array Encoding.natural).encode (chosenWeights node anchor weights index values)).length+
      (Encoding.sequence Encoding.natural (chosenValues node anchor values)).length ≤
    ((Encoding.array Encoding.natural).encode weights).length+
      (Encoding.sequence Encoding.natural values).length := by
  by_cases selected : node.level=anchor
  · cases values with
    | nil => simp [chosenWeights,chosenValues,selected,availableWeights,availableValues]
    | cons value values =>
      have updated := Encoding.array_setIfInBounds_length_le Encoding.natural weights index value
      simp only [chosenWeights,chosenValues,selected,if_true,availableWeights,availableValues,
        Encoding.sequence,List.length_append]
      omega
  · simp [chosenWeights,chosenValues,selected]

@[simp] theorem chosenWeights_size (node : Executable.Node) (anchor : Nat)
    (weights : Array Nat) (index : Nat) (values : List Nat) :
    (chosenWeights node anchor weights index values).size=weights.size := by
  by_cases selected : node.level=anchor
  · cases values <;> simp [chosenWeights,selected,availableWeights]
  · simp [chosenWeights,selected]

def remainingValues (anchor : Nat) : List Executable.Node → List Nat → List Nat
  | [],values => values
  | node::nodes,values => remainingValues anchor nodes (chosenValues node anchor values)

theorem assignScan_cons (node : Executable.Node) (nodes : List Executable.Node) (anchor start : Nat)
    (values : List Nat) (weights : Array Nat) :
    assignScan anchor start (node::nodes) values weights=
      assignScan anchor (start+1) nodes (chosenValues node anchor values)
        (chosenWeights node anchor weights start values) := by
  by_cases selected : node.level=anchor <;> cases values <;>
    simp [assignScan,chosenValues,chosenWeights,availableValues,availableWeights,selected]

end Counting.StackMachine.AuditPropagation
