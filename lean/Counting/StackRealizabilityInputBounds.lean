import Counting.StackRealizabilityInputSplit

namespace Counting.StackMachine.RealizabilityCheck

theorem verifierInput_parts (vista : Executable.Vista) (values : List Nat) (ell order : Nat) :
    (Encoding.verifierInput.encode (vista,values,ell,order)).length=
      ((Encoding.list Encoding.node).encode vista.nodes.toList).length+
      (Encoding.natural.encode vista.bottom).length+
      ((Encoding.list Encoding.natural).encode values).length+
      (Encoding.natural.encode ell).length+(Encoding.natural.encode order).length := by
  simp only [Encoding.verifierInput,Encoding.vista,Encoding.transport,Encoding.product,List.length_append]
  omega

theorem verifierInput_vista_length (vista : Executable.Vista) (values : List Nat) (ell order : Nat) :
    (Encoding.vista.encode vista).length ≤ (Encoding.verifierInput.encode (vista,values,ell,order)).length := by
  simp only [Encoding.verifierInput,Encoding.product,List.length_append];omega

theorem verifierInput_node_weights_length (vista : Executable.Vista) (values : List Nat) (ell order : Nat) :
    ((Encoding.list Encoding.node).encode vista.nodes.toList).length+
      ((Encoding.list Encoding.natural).encode values).length ≤
        (Encoding.verifierInput.encode (vista,values,ell,order)).length := by
  rw [verifierInput_parts];omega

end Counting.StackMachine.RealizabilityCheck
