import Counting.StackRealizabilityVistaRead
import Counting.StackRealizabilityVistaBudget

namespace Counting.StackMachine.VistaComplement
open Routine EncodingPrograms RealizabilityCall
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

def inputFields : Routine 128 := sequence (readField DagParser.vista 0) (readField DagParser.natural 2)

def inputFieldsData (data : Fin 30→List Bool) (vista : Executable.Vista) (ell : Nat) : Fin 30→List Bool :=
  Function.update (Function.update
    (Function.update (Function.update data 5 (Encoding.natural.encode ell)) 0 (Encoding.vista.encode vista))
      5 []) 2 (Encoding.natural.encode ell)

/-- The view and leader count remain serialized and can be copied into
both certificate calls. No agent identities or realized population enter
this input extraction. -/
theorem inputFields_executes (data : Fin 30→List Bool) (vista : Executable.Vista) (ell : Nat)
    (accepted : Bool) (tail : List Bool) (status : data 4=accepted::tail)
    (source : data 5=Encoding.vistaInput.encode (vista,ell)) (emptyVista : data 0=[])
    (emptyLeader : data 2=[]) :
    ∃ time ≤ 8100*((Encoding.vistaInput.encode (vista,ell)).length+1)^4,
      Executes inputFields (file data) time (file (inputFieldsData data vista ell)) := by
  obtain ⟨t0,b0,r0⟩ := readField_executes DagParser.vista data 0 (by decide) (by decide)
    vista (Encoding.natural.encode ell) accepted tail source status emptyVista
  let middle := Function.update (Function.update data 5 (Encoding.natural.encode ell)) 0 (Encoding.vista.encode vista)
  obtain ⟨t1,b1,r1⟩ := readField_executes DagParser.natural middle 2 (by decide) (by decide)
    ell [] accepted tail (by simp [middle]) (by simp [middle,status]) (by simp [middle,emptyLeader])
  let L := (Encoding.vistaInput.encode (vista,ell)).length
  have lengths : L=(Encoding.vista.encode vista).length+(Encoding.natural.encode ell).length := by
    exact List.length_append
  have firstCost := fieldReaderCost_le DagParser.vista.coefficient DagParser.vista.exponent
    (data 5).length (Encoding.vista.encode vista).length L vistaParser_coefficient vistaParser_degree
      (by rw [source]) (by omega)
  have secondCost := fieldReaderCost_le DagParser.natural.coefficient DagParser.natural.exponent
    (middle 5).length (Encoding.natural.encode ell).length L naturalParser_coefficient naturalParser_degree
      (by simp only [middle,Function.update_of_ne (show (5:Fin 30)≠0 by decide),Function.update_self];omega) (by omega)
  have bound0 := b0.trans firstCost
  have bound1 := b1.trans secondCost
  have one : 1 ≤ (L+1)^4 := Nat.one_le_pow _ _ (by omega)
  refine ⟨_,?_,r0.sequence r1⟩
  change t0+1+t1 ≤ 8100*(L+1)^4
  omega

end Counting.StackMachine.VistaComplement
