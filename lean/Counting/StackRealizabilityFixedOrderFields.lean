import Counting.StackRealizabilityVistaRead
import Counting.StackRealizabilityVistaBudget
import Counting.StackRealizabilityExternalFields

namespace Counting.StackMachine.FixedOrderRecognition
open Routine EncodingPrograms RealizabilityCall VistaComplement
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def inputFields : Routine 128 := sequence (readField DagParser.vista 0)
  (sequence (readField DagParser.natural 2) (readField DagParser.natural 3))

def inputFieldsData (data : Fin 30→List Bool) (vista : Executable.Vista) (ell order : Nat) : Fin 30→List Bool :=
  Function.update (Function.update
    (Function.update (Function.update
      (Function.update (Function.update data 5 (Encoding.natural.encode ell++Encoding.natural.encode order))
        0 (Encoding.vista.encode vista)) 5 (Encoding.natural.encode order)) 2 (Encoding.natural.encode ell)) 5 [])
      3 (Encoding.natural.encode order)

theorem inputFields_executes (data : Fin 30→List Bool) (vista : Executable.Vista) (ell order : Nat)
    (accepted : Bool) (tail : List Bool) (status : data 4=accepted::tail)
    (source : data 5=Encoding.fixedOrderInput.encode (vista,ell,order))
    (emptyVista : data 0=[]) (emptyLeader : data 2=[]) (emptyOrder : data 3=[]) :
    ∃time≤12100*((Encoding.fixedOrderInput.encode (vista,ell,order)).length+1)^4,
      Executes inputFields (file data) time (file (inputFieldsData data vista ell order)) := by
  obtain ⟨t0,b0,r0⟩ := readField_executes DagParser.vista data 0 (by decide) (by decide)
    vista (Encoding.natural.encode ell++Encoding.natural.encode order) accepted tail source status emptyVista
  let d1 := Function.update (Function.update data 5 (Encoding.natural.encode ell++Encoding.natural.encode order))
    0 (Encoding.vista.encode vista)
  obtain ⟨t1,b1,r1⟩ := readField_executes DagParser.natural d1 2 (by decide) (by decide)
    ell (Encoding.natural.encode order) accepted tail (by simp [d1])
      (by simp [d1,status]) (by simp [d1,emptyLeader])
  let d2 := Function.update (Function.update d1 5 (Encoding.natural.encode order)) 2 (Encoding.natural.encode ell)
  obtain ⟨t2,b2,r2⟩ := readField_executes DagParser.natural d2 3 (by decide) (by decide)
    order [] accepted tail (by simp [d2]) (by simp [d2,d1,status]) (by simp [d2,d1,emptyOrder])
  let L := (Encoding.fixedOrderInput.encode (vista,ell,order)).length
  have lengthEq : L=(Encoding.vista.encode vista).length+(Encoding.natural.encode ell).length+
      (Encoding.natural.encode order).length := by
    simp only [L,Encoding.fixedOrderInput,Encoding.product,List.length_append];omega
  have s0 : (data 5).length≤L := by rw [source]
  have s1 : (d1 5).length≤L := by simp only [d1,Function.update_of_ne (show (5:Fin 30)≠0 by decide),Function.update_self,List.length_append];omega
  have s2 : (d2 5).length≤L := by simp only [d2,Function.update_of_ne (show (5:Fin 30)≠2 by decide),Function.update_self];omega
  have c0 := b0.trans (fieldReaderCost_le _ _ _ _ L vistaParser_coefficient vistaParser_degree s0 (by omega))
  have c1 := b1.trans (fieldReaderCost_le _ _ _ _ L naturalParser_coefficient naturalParser_degree s1 (by omega))
  have c2 := b2.trans (fieldReaderCost_le _ _ _ _ L naturalParser_coefficient naturalParser_degree s2 (by omega))
  have one : 1≤(L+1)^4 := Nat.one_le_pow _ _ (by omega)
  refine ⟨_,?_,r0.sequence (r1.sequence r2)⟩
  change t0+1+(t1+1+t2)≤12100*(L+1)^4
  omega

def allFields : Routine 128 := sequence (copyExternal 8 5) (sequence inputFields (copyExternal 9 1))
def allFieldsData (data : Fin 30→List Bool) (vista : Executable.Vista) (ell order : Nat) : Fin 30→List Bool :=
  Function.update (inputFieldsData (Function.update data 5 (data 8)) vista ell order) 1 (data 9)

theorem allFields_executes (data : Fin 30→List Bool) (vista : Executable.Vista) (ell order : Nat)
    (accepted : Bool) (tail : List Bool) (status : data 4=accepted::tail)
    (source : data 8=Encoding.fixedOrderInput.encode (vista,ell,order))
    (empty : ∀i:Fin 30,i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=5 → data i=[]) :
    ∃time≤12200*((data 8).length+(data 9).length+1)^4,
      Executes allFields (file data) time (file (allFieldsData data vista ell order)) := by
  have r0 := copyExternal_executes data 8 5 (by decide)
  rw [empty 5 (by simp),List.append_nil] at r0
  let d1 := Function.update data 5 (data 8)
  obtain ⟨t1,b1,r1⟩ := inputFields_executes d1 vista ell order accepted tail
    (by simp [d1,status]) (by simpa [d1] using source)
    (by simpa [d1] using empty 0 (by simp)) (by simpa [d1] using empty 2 (by simp))
    (by simpa [d1] using empty 3 (by simp))
  let d2 := inputFieldsData d1 vista ell order
  have r2 := copyExternal_executes d2 9 1 (by decide)
  have preserved : d2 9=data 9 := by simp [d2,inputFieldsData,d1]
  rw [preserved,show d2 1=[] by simp [d2,inputFieldsData,d1,empty 1 (by simp)],List.append_nil] at r2
  rw [←source] at b1
  let L := (data 8).length+(data 9).length
  have bound := b1.trans (Nat.mul_le_mul_left 12100 (Nat.pow_le_pow_left (show (data 8).length+1≤L+1 by dsimp only [L];omega) 4))
  have linear : L+1≤(L+1)^4 := Nat.le_self_pow (by decide) _
  refine ⟨_,?_,r0.sequence (r1.sequence r2)⟩
  change 5*(data 8).length+2+1+(t1+1+(5*(data 9).length+2))≤12200*(L+1)^4
  have base : L=(data 8).length+(data 9).length := rfl
  omega

end Counting.StackMachine.FixedOrderRecognition
