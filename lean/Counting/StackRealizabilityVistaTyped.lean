import Counting.StackRealizabilityVistaAllFields
import Counting.StackRealizabilityVistaChecks

namespace Counting.StackMachine.VistaComplement
open Routine RealizabilityCall
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 2400000

def typedBody : Routine 128 := sequence allFields checks

def typedCoefficient : Nat := checksCoefficient+25001

theorem typedBody_executes (data : Fin 30→List Bool) (vista : Executable.Vista)
    (ell first second : Nat) (a b : List Nat) (accepted : Bool) (tail : List Bool)
    (status : data 4=accepted::tail)
    (input : data 8=Encoding.vistaInput.encode (vista,ell))
    (witness : data 9=Encoding.twoOrderWitness.encode ((first,a),(second,b)))
    (empty : ∀i:Fin 30,i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=5 ∨ i=6 ∨ i=7 → data i=[]) :
    ∃time≤Complexity.polynomial typedCoefficient 25 ((data 8).length+(data 9).length),
      ∃result, Executes typedBody (file data) time (file result) ∧
        result 4=(accepted && Encoding.verifyTwoOrders vista ell ((first,a),(second,b)))::tail := by
  obtain ⟨t0,b0,r0⟩ := allFields_executes data vista ell first second a b accepted tail status input witness empty
  let parsed := allFieldsData data vista ell first second a b
  have p0 : parsed 0=Encoding.vista.encode vista := by
    simp [parsed,allFieldsData,witnessFieldsData,orderFieldsData,inputFieldsData]
  have p1 : parsed 1=(Encoding.list Encoding.natural).encode a := by
    simp [parsed,allFieldsData,witnessFieldsData,orderFieldsData,inputFieldsData]
  have p2 : parsed 2=Encoding.natural.encode ell := by
    simp [parsed,allFieldsData,witnessFieldsData,orderFieldsData,inputFieldsData]
  have p3 : parsed 3=Encoding.natural.encode first := by
    simp [parsed,allFieldsData,witnessFieldsData,orderFieldsData,inputFieldsData]
  have p6 : parsed 6=Encoding.natural.encode second := by
    simp [parsed,allFieldsData,witnessFieldsData,orderFieldsData,inputFieldsData]
  have p7 : parsed 7=(Encoding.list Encoding.natural).encode b := by
    simp [parsed,allFieldsData,witnessFieldsData,orderFieldsData,inputFieldsData]
  have p4 : parsed 4=accepted::tail := by
    simp [parsed,allFieldsData,witnessFieldsData,orderFieldsData,inputFieldsData,status]
  obtain ⟨t1,b1,r1⟩ := checks_executes parsed vista ell first second a b p0 p1 p2 p3 p6 p7 accepted tail p4
  have lengthEq : fieldsLength parsed=(data 8).length+(data 9).length := by
    simp only [fieldsLength,p0,p1,p2,p3,p6,p7,input,witness,
      Encoding.vistaInput,Encoding.twoOrderWitness,Encoding.orderWitness,Encoding.product,List.length_append]
    omega
  rw [lengthEq] at b1
  let L := (data 8).length+(data 9).length
  have power : (L+1)^4≤(L+1)^25 := Nat.pow_le_pow_right (by omega) (by decide)
  have bound0 := b0.trans (Nat.mul_le_mul_left 25000 power)
  have one : 1≤(L+1)^25 := Nat.one_le_pow _ _ (by omega)
  refine ⟨t0+1+t1,?_,_,r0.sequence r1,by simp⟩
  change _≤(checksCoefficient+25001)*(L+1)^25
  change t1≤checksCoefficient*(L+1)^25 at b1
  simp only [Nat.add_mul]
  omega

end Counting.StackMachine.VistaComplement
