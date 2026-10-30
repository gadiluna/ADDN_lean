import Counting.EncodingRecognition
import Counting.StackRealizabilityCallSpec
import Counting.StackRealizabilityVistaSecond
import Counting.StackRealizabilityVistaDifferent

namespace Counting.StackMachine.VistaComplement
open Routine RealizabilityCall
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 2200000

def checks : Routine 128 := sequence ordersDifferent
  (sequence RealizabilityCall.check (sequence secondFields RealizabilityCall.check))

def fieldsLength (data : Fin 30→List Bool) : Nat :=
  (data 0).length+(data 1).length+(data 2).length+(data 3).length+(data 6).length+(data 7).length

def checksCoefficient : Nat := 2*RealizabilityCall.coefficient+100

/-- Both calls run the proved compact verifier; the second call physically
replaces the first certificate fields. All other caller data are retained. -/
theorem checks_executes (data : Fin 30→List Bool) (vista : Executable.Vista)
    (ell first second : Nat) (a b : List Nat)
    (viewField : data 0=Encoding.vista.encode vista)
    (firstCounts : data 1=(Encoding.list Encoding.natural).encode a)
    (leaderField : data 2=Encoding.natural.encode ell)
    (firstOrder : data 3=Encoding.natural.encode first)
    (secondOrder : data 6=Encoding.natural.encode second)
    (secondCounts : data 7=(Encoding.list Encoding.natural).encode b)
    (accepted : Bool) (tail : List Bool) (status : data 4=accepted::tail) :
    ∃time≤Complexity.polynomial checksCoefficient 25 (fieldsLength data),
      Executes checks (file data) time
        (file (Function.update (secondFieldsData data) 4
          ((accepted && Encoding.verifyTwoOrders vista ell ((first,a),(second,b)))::tail))) := by
  let diff := first != second
  let passA := RealizabilityVerifier.verify vista a.toArray ell first
  let passB := RealizabilityVerifier.verify vista b.toArray ell second
  obtain ⟨t0,b0,r0⟩ := ordersDifferent_executes data accepted tail status
  rw [firstOrder,secondOrder,canonical_orders_different] at r0
  rw [firstOrder,secondOrder] at b0
  let d1 := Function.update data 4 ((accepted && diff)::tail)
  obtain ⟨t1,b1,r1⟩ := check_typed d1 vista a ell first
    (by simpa [d1] using viewField) (by simpa [d1] using firstCounts)
    (by simpa [d1] using leaderField) (by simpa [d1] using firstOrder)
    (accepted && diff) tail (by simp [d1])
  let d2 := Function.update d1 4 (((accepted && diff) && passA)::tail)
  have r2 := secondFields_executes d2
  let d3 := secondFieldsData d2
  obtain ⟨t3,b3,r3⟩ := check_typed d3 vista b ell second
    (by simpa [d3,secondFieldsData,d2,d1] using viewField)
    (by simpa [d3,secondFieldsData,d2,d1] using secondCounts)
    (by simpa [d3,secondFieldsData,d2,d1] using leaderField)
    (by simpa [d3,secondFieldsData,d2,d1] using secondOrder)
    ((accepted && diff) && passA) tail (by simp [d3,secondFieldsData,d2])
  have final : Function.update d3 4 ((((accepted && diff) && passA) && passB)::tail)=
      Function.update (secondFieldsData data) 4
        ((accepted && Encoding.verifyTwoOrders vista ell ((first,a),(second,b)))::tail) := by
    funext i
    by_cases i=4 <;> by_cases i=1 <;> by_cases i=3 <;>
      simp_all [d3,d2,d1,secondFieldsData,Encoding.verifyTwoOrders,diff,passA,passB,Bool.and_assoc]
  rw [final] at r3
  let L := fieldsLength data
  have lenA : (Encoding.verifierInput.encode (vista,a,ell,first)).length≤L := by
    rw [←encodedInput_fields data vista a ell first viewField firstCounts leaderField firstOrder]
    simp only [encodedInput,List.length_append,L,fieldsLength];omega
  have lenB : (Encoding.verifierInput.encode (vista,b,ell,second)).length≤L := by
    change (Encoding.vista.encode vista++((Encoding.list Encoding.natural).encode b++
      (Encoding.natural.encode ell++Encoding.natural.encode second))).length≤_
    rw [←viewField,←secondCounts,←leaderField,←secondOrder]
    simp only [List.length_append,L,fieldsLength];omega
  have bound1 : t1≤RealizabilityCall.coefficient*(L+1)^25 :=
    b1.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 25))
  have bound3 : t3≤RealizabilityCall.coefficient*(L+1)^25 :=
    b3.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 25))
  have small : (Encoding.natural.encode first).length+(Encoding.natural.encode second).length≤L := by
    rw [←firstOrder,←secondOrder];dsimp only [L,fieldsLength];omega
  have linear : L+1≤(L+1)^25 := Nat.le_self_pow (by decide) _
  refine ⟨_,?_,r0.sequence (r1.sequence (r2.sequence r3))⟩
  simp only [d2,d1,Function.update_of_ne (show (1:Fin 30)≠4 by decide),
    Function.update_of_ne (show (3:Fin 30)≠4 by decide),
    Function.update_of_ne (show (7:Fin 30)≠4 by decide),
    Function.update_of_ne (show (6:Fin 30)≠4 by decide)]
  change _≤(2*RealizabilityCall.coefficient+100)*(L+1)^25
  simp only [Nat.add_mul,Nat.mul_assoc]
  have lengths : (data 1).length+(data 3).length+(data 7).length+(data 6).length≤L := by
    dsimp only [L,fieldsLength];omega
  omega

end Counting.StackMachine.VistaComplement
