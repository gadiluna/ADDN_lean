import Counting.StackAuditPropagationInput
import Counting.AuditPropagationAssignedSize
import Counting.PropagationEncodingBounds

namespace Counting.StackMachine.AuditPropagation

theorem propagationInput_length (anchor : Nat) (vista : Executable.Vista) (values : Array Nat) :
    (propagationInputWord anchor vista values).length=
      2*anchor.size+1+(2*(Encoding.vista.encode vista).length+1)+
      (2*values.size.size+1)+(Encoding.sequence Encoding.natural values.toList).length := by
  simp only [propagationInputWord,propagationInputCodec,Encoding.product,Encoding.framed,
    List.length_append,Encoding.natural_length,Encoding.frame_length,Encoding.array,
    Encoding.transport,Encoding.list,Array.length_toList]
  omega

theorem assigned_input_encoded_length (anchor : Nat) (vista : Executable.Vista) (values : Array Nat) :
    ((Encoding.array Encoding.natural).encode (assigned vista anchor values)).length ≤
      5*((propagationInputWord anchor vista values).length+1) := by
  have inputSize:=propagationInput_length anchor vista values
  have count:=Encoding.vista_nodes_le_length vista
  have bits : vista.nodes.size.size ≤ vista.nodes.size := Nat.size_le.mpr Nat.lt_two_pow_self
  have assignedSize:=assigned_encoded_length vista anchor values
  have zeroLength : ((Encoding.array Encoding.natural).encode (Array.replicate vista.nodes.size 0)).length=
      2*vista.nodes.size.size+1+vista.nodes.size := by
    simp only [zero_array_word,List.length_append,Encoding.natural_length,List.length_replicate]
  rw [zeroLength] at assignedSize
  omega

/-- The complete propagated output, including its array header, has a
cubic bound in the serialized input to the actual propagation machine. -/
theorem propagateWeights_input_encoded_length (anchor : Nat) (vista : Executable.Vista) (values : Array Nat)
    (fits : anchor ≤ vista.nodes.size) :
    ((Encoding.array Encoding.natural).encode (Executable.propagateWeights vista anchor values)).length ≤
      1080*((propagationInputWord anchor vista values).length+1)^3 := by
  have assignedSize:=assigned_input_encoded_length anchor vista values
  have result:=Executable.propagateDown_encoded_polynomial vista (assigned vista anchor values) anchor
    (by simp [assigned,Executable.assignEntries_size]) fits
  rw [Executable.propagateWeights_eq_fold]
  change ((Encoding.array Encoding.natural).encode
    (Executable.propagateDown vista anchor (assigned vista anchor values))).length ≤ _
  have raised:=Nat.pow_le_pow_left (by omega :
    ((Encoding.array Encoding.natural).encode (assigned vista anchor values)).length+1 ≤
      6*((propagationInputWord anchor vista values).length+1)) 3
  nlinarith only [result,raised]

end Counting.StackMachine.AuditPropagation
