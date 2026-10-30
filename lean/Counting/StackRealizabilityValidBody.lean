import Counting.StackRealizabilityShapeGate
import Counting.StackRealizabilityInputBounds

namespace Counting.StackMachine.RealizabilityCheck
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 2200000

def validBody : Routine 98 := sequence inputNodes
  (sequence inputCount (sequence inputShape shapeGate))

/-- The valid-DAG branch still checks the supplied count array itself.
A mismatch or zero count is rejected without entering the round scans. -/
theorem validBody_executes (vista : Executable.Vista) (values : List Nat) (ell order : Nat)
    (valid : vista.valid=true) :
    ∃ time ≤ Complexity.polynomial (typedCoefficient+12000) 25
        (Encoding.verifierInput.encode (vista,values,ell,order)).length,
      ∃ result : Store 98,
        Executes validBody (inputFieldsStore vista values ell order [true]) time result ∧
        result 1=[] ∧ result 85=[countsShapeCheck values.toArray vista.nodes.size &&
          typedChecks vista values ell order] := by
  obtain ⟨t0,b0,r0⟩ := inputNodes_executes vista values ell order true []
  obtain ⟨t1,b1,r1⟩ := inputCount_executes vista values ell order true []
  obtain ⟨t2,b2,r2⟩ := inputShape_executes vista values ell order true []
  simp only [Bool.true_and] at r2
  obtain ⟨t3,b3,result,r3,empty,status⟩ := shapeGate_executes vista values ell order valid
  refine ⟨_,?_,result,r0.sequence (r1.sequence (r2.sequence r3)),empty,status⟩
  let B := (Encoding.verifierInput.encode (vista,values,ell,order)).length+1
  have vistaBound := verifierInput_vista_length vista values ell order
  have parts := verifierInput_node_weights_length vista values ell order
  have positive : 1 ≤ B := by dsimp only [B];omega
  have bound0 : t0 ≤ 4000*B^25 := b0.trans (Nat.mul_le_mul_left _
    ((Nat.pow_le_pow_left (by dsimp only [B];omega) 4).trans
      (Nat.pow_le_pow_right positive (by decide))))
  have bound1 : t1 ≤ 1900*B^25 := b1.trans (Nat.mul_le_mul_left _
    ((Nat.pow_le_pow_left (by dsimp only [B];omega) 3).trans
      (Nat.pow_le_pow_right positive (by decide))))
  have bound2 : t2 ≤ 5000*B^25 := b2.trans (Nat.mul_le_mul_left _
    ((Nat.pow_le_pow_left (by dsimp only [B];omega) 3).trans
      (Nat.pow_le_pow_right positive (by decide))))
  change t3 ≤ (typedCoefficient+3)*B^25 at b3
  have one := Nat.one_le_pow 25 B positive
  change t0+1+(t1+1+(t2+1+t3)) ≤ (typedCoefficient+12000)*B^25
  rw [Nat.add_mul] at b3 ⊢
  omega

end Counting.StackMachine.RealizabilityCheck
