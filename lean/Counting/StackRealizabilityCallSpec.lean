import Counting.StackRealizabilityCall

namespace Counting.StackMachine.RealizabilityCall
open Routine

theorem encodedInput_fields (data : Fin 30→List Bool) (vista : Executable.Vista)
    (values : List Nat) (ell order : Nat)
    (viewField : data 0=Encoding.vista.encode vista)
    (countsField : data 1=(Encoding.list Encoding.natural).encode values)
    (leaderField : data 2=Encoding.natural.encode ell)
    (orderField : data 3=Encoding.natural.encode order) :
    encodedInput data=Encoding.verifierInput.encode (vista,values,ell,order) := by
  simp only [encodedInput,viewField,countsField,leaderField,orderField,
    Encoding.verifierInput,Encoding.product,List.append_assoc]

theorem check_typed (data : Fin 30→List Bool) (vista : Executable.Vista)
    (values : List Nat) (ell order : Nat)
    (viewField : data 0=Encoding.vista.encode vista)
    (countsField : data 1=(Encoding.list Encoding.natural).encode values)
    (leaderField : data 2=Encoding.natural.encode ell)
    (orderField : data 3=Encoding.natural.encode order)
    (accepted : Bool) (tail : List Bool) (status : data 4=accepted::tail) :
    ∃ time ≤ Complexity.polynomial coefficient 25
        (Encoding.verifierInput.encode (vista,values,ell,order)).length,
      Executes check (file data) time
        (file (Function.update data 4 ((accepted && RealizabilityVerifier.verify vista values.toArray ell order)::tail))) := by
  have execution := check_executes data accepted tail status
  rw [encodedInput_fields data vista values ell order viewField countsField leaderField orderField,
    RealizabilityCheck.encodedVerifier_encode] at execution
  exact execution

end Counting.StackMachine.RealizabilityCall
