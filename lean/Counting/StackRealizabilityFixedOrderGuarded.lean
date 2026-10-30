import Counting.StackRealizabilityFixedOrderGuard

namespace Counting.StackMachine.FixedOrderRecognition
open Routine RealizabilityCall
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1800000

def guarded : Routine 128 := sequence syntaxChecks typedGate

def guardedCoefficient : Nat := syntaxCoefficient+typedCoefficient+4

theorem guarded_executes (data : Fin 30→List Bool) (accepted : Bool) (tail : List Bool)
    (status : data 4=accepted::tail)
    (empty : ∀i:Fin 30,i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=5 → data i=[]) :
    ∃time≤Complexity.polynomial guardedCoefficient 25 ((data 8).length+(data 9).length),
      ∃result, Executes guarded (file data) time (file result) ∧
        result 4=(accepted && Encoding.binaryFixedOrderVerifier (data 8) (data 9))::tail := by
  obtain ⟨t0,b0,r0⟩ := syntaxChecks_executes data accepted tail status
  let middle := Function.update data 4 ((accepted && syntaxAccepted (data 8) (data 9))::tail)
  have original8 : middle 8=data 8 := by simp [middle]
  have original9 : middle 9=data 9 := by simp [middle]
  obtain ⟨t1,b1,result,r1,output⟩ := typedGate_executes middle accepted tail
    (by simp [middle]) (by
      intro i hi
      have ne:i≠4 := by rcases hi with h|h|h|h|h <;> subst i <;> decide
      simpa [middle,ne] using empty i hi)
  rw [original8,original9] at b1 output
  refine ⟨t0+1+t1,?_,result,r0.sequence r1,output⟩
  have one : 1≤((data 8).length+(data 9).length+1)^25 := Nat.one_le_pow _ _ (by omega)
  simp only [Complexity.polynomial,guardedCoefficient,Nat.add_mul] at b0 b1 ⊢
  omega

end Counting.StackMachine.FixedOrderRecognition
