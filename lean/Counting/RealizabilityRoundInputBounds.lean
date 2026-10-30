import Counting.StackRealizabilityRoundAll
import Counting.EncodingVerifier

namespace Counting.StackMachine.RealizabilityCheck

/-- The all-round budget is controlled by the complete real verifier input.
Neither certificate acceptance nor a matching count-array length is assumed. -/
theorem allRoundsSize_input_bound (vista : Executable.Vista) (weights : Array Nat)
    (ell N : Nat) (valid : vista.valid=true) :
    allRoundsSize vista weights N ≤
      5*((Encoding.verifierInput.encode (vista,weights.toList,ell,N)).length+1) := by
  let L:=(Encoding.verifierInput.encode (vista,weights.toList,ell,N)).length
  have whole : L=
      ((Encoding.list Encoding.node).encode vista.nodes.toList).length+
      (Encoding.natural.encode vista.bottom).length+
      ((Encoding.list Encoding.natural).encode weights.toList).length+
      (Encoding.natural.encode ell).length+(Encoding.natural.encode N).length := by
    simp only [L,Encoding.verifierInput,Encoding.vista,Encoding.transport,
      Encoding.product,List.length_append]
    omega
  have nodes:=Encoding.vista_nodes_le_length vista
  have vistaLength : (Encoding.vista.encode vista).length ≤ L := by
    simp only [L,Encoding.verifierInput,Encoding.product,List.length_append]
    omega
  have depth:=(RealizabilityVerifier.valid_depth_lt_size vista valid).le
  have order : N.size ≤ L := by
    simp only [Encoding.natural_length] at whole
    omega
  have mass : massInputSize vista.nodes.toList weights.toList ≤ L+1 := by
    unfold massInputSize
    omega
  unfold allRoundsSize
  change _ ≤ 5*(L+1)
  omega

end Counting.StackMachine.RealizabilityCheck
