import Counting.StackRealizabilityExternalFields
import Counting.StackRealizabilityVistaFields
import Counting.StackRealizabilityWitnessFields

namespace Counting.StackMachine.VistaComplement
open Routine RealizabilityCall
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1800000

def allFields : Routine 128 := sequence (copyExternal 8 5)
  (sequence inputFields (sequence (copyExternal 9 5) witnessFields))

def allFieldsData (data : Fin 30→List Bool) (vista : Executable.Vista) (ell first second : Nat)
    (a b : List Nat) : Fin 30→List Bool :=
  witnessFieldsData (Function.update
    (inputFieldsData (Function.update data 5 (data 8)) vista ell) 5 (data 9)) first second a b

theorem allFields_executes (data : Fin 30→List Bool) (vista : Executable.Vista)
    (ell first second : Nat) (a b : List Nat) (accepted : Bool) (tail : List Bool)
    (status : data 4=accepted::tail)
    (input : data 8=Encoding.vistaInput.encode (vista,ell))
    (witness : data 9=Encoding.twoOrderWitness.encode ((first,a),(second,b)))
    (empty : ∀i:Fin 30,i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=5 ∨ i=6 ∨ i=7 → data i=[]) :
    ∃ time ≤ 25000*((data 8).length+(data 9).length+1)^4,
      Executes allFields (file data) time (file (allFieldsData data vista ell first second a b)) := by
  have r0 := copyExternal_executes data 8 5 (by decide)
  rw [empty 5 (by simp),List.append_nil] at r0
  let d1 := Function.update data 5 (data 8)
  obtain ⟨t1,b1,r1⟩ := inputFields_executes d1 vista ell accepted tail
    (by simp [d1,status]) (by simpa [d1] using input)
    (by simpa [d1] using empty 0 (by simp)) (by simpa [d1] using empty 2 (by simp))
  let d2 := inputFieldsData d1 vista ell
  have r2 := copyExternal_executes d2 9 5 (by decide)
  have source : d2 9=data 9 := by simp [d2,d1,inputFieldsData]
  rw [source,show d2 5=[] by simp [d2,inputFieldsData],List.append_nil] at r2
  let d3 := Function.update d2 5 (data 9)
  obtain ⟨t3,b3,r3⟩ := witnessFields_executes d3 first second a b accepted tail
    (by simp [d3,d2,d1,inputFieldsData,status]) (by simpa [d3] using witness)
    (by simpa [d3,d2,d1,inputFieldsData] using empty 3 (by simp))
    (by simpa [d3,d2,d1,inputFieldsData] using empty 1 (by simp))
    (by simpa [d3,d2,d1,inputFieldsData] using empty 6 (by simp))
    (by simpa [d3,d2,d1,inputFieldsData] using empty 7 (by simp))
  let L := (data 8).length+(data 9).length
  rw [←input] at b1
  rw [←witness] at b3
  have small1 : (data 8).length+1≤L+1 := by dsimp only [L];omega
  have small3 : (data 9).length+1≤L+1 := by dsimp only [L];omega
  have bound1 := b1.trans (Nat.mul_le_mul_left 8100 (Nat.pow_le_pow_left small1 4))
  have bound3 := b3.trans (Nat.mul_le_mul_left 16300 (Nat.pow_le_pow_left small3 4))
  have linear : L+1≤(L+1)^4 := Nat.le_self_pow (by decide) _
  refine ⟨_,?_,r0.sequence (r1.sequence (r2.sequence r3))⟩
  change 5*(data 8).length+2+1+(t1+1+(5*(data 9).length+2+1+t3))≤25000*(L+1)^4
  dsimp only [L] at linear bound1 bound3 ⊢
  omega

end Counting.StackMachine.VistaComplement
