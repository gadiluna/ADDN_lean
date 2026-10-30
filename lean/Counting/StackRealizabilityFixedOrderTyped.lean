import Counting.StackRealizabilityFixedOrderFields
import Counting.StackRealizabilityCallSpec

namespace Counting.StackMachine.FixedOrderRecognition
open Routine RealizabilityCall
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1800000

def typedBody : Routine 128 := sequence allFields RealizabilityCall.check
def typedCoefficient : Nat := RealizabilityCall.coefficient+12201

theorem typedBody_executes (data : Fin 30→List Bool) (vista : Executable.Vista) (ell order : Nat)
    (counts : List Nat) (accepted : Bool) (tail : List Bool) (status : data 4=accepted::tail)
    (source : data 8=Encoding.fixedOrderInput.encode (vista,ell,order))
    (witness : data 9=(Encoding.list Encoding.natural).encode counts)
    (empty : ∀i:Fin 30,i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=5 → data i=[]) :
    ∃time≤Complexity.polynomial typedCoefficient 25 ((data 8).length+(data 9).length),
      ∃result, Executes typedBody (file data) time (file result) ∧
        result 4=(accepted && RealizabilityVerifier.verify vista counts.toArray ell order)::tail := by
  obtain ⟨t0,b0,r0⟩ := allFields_executes data vista ell order accepted tail status source empty
  let parsed := allFieldsData data vista ell order
  have p0 : parsed 0=Encoding.vista.encode vista := by simp [parsed,allFieldsData,inputFieldsData]
  have p1 : parsed 1=(Encoding.list Encoding.natural).encode counts := by simp [parsed,allFieldsData,witness]
  have p2 : parsed 2=Encoding.natural.encode ell := by simp [parsed,allFieldsData,inputFieldsData]
  have p3 : parsed 3=Encoding.natural.encode order := by simp [parsed,allFieldsData,inputFieldsData]
  have p4 : parsed 4=accepted::tail := by simp [parsed,allFieldsData,inputFieldsData,status]
  obtain ⟨t1,b1,r1⟩ := check_typed parsed vista counts ell order p0 p1 p2 p3 accepted tail p4
  have lengths : (Encoding.verifierInput.encode (vista,counts,ell,order)).length=
      (data 8).length+(data 9).length := by
    simp only [source,witness,Encoding.verifierInput,Encoding.fixedOrderInput,Encoding.product,List.length_append]
    omega
  rw [lengths] at b1
  let L := (data 8).length+(data 9).length
  have power : (L+1)^4≤(L+1)^25 := Nat.pow_le_pow_right (by omega) (by decide)
  have bound0 := b0.trans (Nat.mul_le_mul_left 12200 power)
  have one : 1≤(L+1)^25 := Nat.one_le_pow _ _ (by omega)
  refine ⟨t0+1+t1,?_,_,r0.sequence r1,by simp⟩
  change _≤(RealizabilityCall.coefficient+12201)*(L+1)^25
  change t1≤RealizabilityCall.coefficient*(L+1)^25 at b1
  simp only [Nat.add_mul]
  omega

end Counting.StackMachine.FixedOrderRecognition
