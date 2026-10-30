import Counting.StackRealizabilityValidBody
import Counting.StackRealizabilityStatusOutput

namespace Counting.StackMachine.RealizabilityCheck
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def validationGate : Routine 98 := branchRead 85 validBody (skip 98)

theorem validationGate_executes (vista : Executable.Vista) (values : List Nat) (ell order : Nat) :
    ∃ time ≤ Complexity.polynomial (typedCoefficient+12003) 25
        (Encoding.verifierInput.encode (vista,values,ell,order)).length,
      ∃ result : Store 98,
        Executes validationGate (inputFieldsStore vista values ell order [vista.valid]) time result ∧
        result 1=[] ∧ result 85=[checkedVerifier vista values.toArray ell order] := by
  let input := inputFieldsStore vista values ell order [vista.valid]
  have flag : input 85=[vista.valid] := by simp [input,inputFieldsStore]
  have one : 1 ≤ ((Encoding.verifierInput.encode (vista,values,ell,order)).length+1)^25 :=
    Nat.one_le_pow _ _ (by omega)
  cases valid : vista.valid with
  | false =>
    have selected : Executes (if false then validBody else skip 98) input 0 input := skip_executes input
    have branch := branchRead_executes (85:Fin 100) validBody (skip 98) false [] input input 0
      (by simpa only [valid] using flag) selected
    refine ⟨3,?_,input,?_,?_,?_⟩
    · unfold Complexity.polynomial;rw [Nat.add_mul];omega
    · simpa only [validationGate,input,valid] using branch
    · simp [input,inputFieldsStore]
    · simp [input,inputFieldsStore,checkedVerifier,valid]
  | true =>
    obtain ⟨time,bound,result,run,empty,status⟩ := validBody_executes vista values ell order valid
    have selected : Executes (if true then validBody else skip 98) input time result := by
      change Executes validBody input time result
      simpa only [input,valid] using run
    have branch := branchRead_executes (85:Fin 100) validBody (skip 98) true [] input result time
      (by simpa only [valid] using flag) selected
    refine ⟨time+3,?_,result,?_,empty,?_⟩
    · unfold Complexity.polynomial at bound ⊢;rw [Nat.add_mul] at bound ⊢;omega
    · simpa only [validationGate,input,valid] using branch
    · simpa only [checkedVerifier,valid,Bool.true_and,List.toList_toArray,typedChecks,Bool.and_assoc] using status

def canonicalCheck : Routine 98 := sequence inputSplit
  (sequence inputValidate (sequence validationGate statusOutput))

def canonicalCoefficient : Nat := typedCoefficient+225000000

/-- The semantic verifier is total on every canonically decoded tuple:
invalid DAGs and invalid count arrays are rejected by physical branches.
The final Boolean is exactly the original compact verifier. -/
theorem canonicalCheck_executes (vista : Executable.Vista) (values : List Nat) (ell order : Nat) :
    ∃ time ≤ Complexity.polynomial canonicalCoefficient 25
        (Encoding.verifierInput.encode (vista,values,ell,order)).length,
      ∃ result : Store 98,
        Executes canonicalCheck
          (inputSplitStore (Encoding.verifierInput.encode (vista,values,ell,order)) [true]) time result ∧
        result 1=[RealizabilityVerifier.verify vista values.toArray ell order] := by
  obtain ⟨t0,b0,r0⟩ := inputSplit_executes vista values ell order true []
  obtain ⟨t1,b1,r1⟩ := inputValidate_executes vista values ell order true []
  simp only [Bool.true_and] at r1
  obtain ⟨t2,b2,result,r2,empty,status⟩ := validationGate_executes vista values ell order
  obtain ⟨finish,output,answer⟩ := statusOutput_executes result _ empty status
  rw [checkedVerifier_eq] at answer
  refine ⟨_,?_,finish,r0.sequence (r1.sequence (r2.sequence output)),answer⟩
  let B := (Encoding.verifierInput.encode (vista,values,ell,order)).length+1
  have positive : 1 ≤ B := by dsimp only [B];omega
  have bound0 : t0 ≤ 6000*B^25 := b0.trans (Nat.mul_le_mul_left _
    (Nat.pow_le_pow_right positive (by decide)))
  have vistaBound := verifierInput_vista_length vista values ell order
  have bound1 : t1 ≤ 224000000*B^25 := b1.trans (Nat.mul_le_mul_left _
    ((Nat.pow_le_pow_left (by dsimp only [B];omega) 6).trans
      (Nat.pow_le_pow_right positive (by decide))))
  change t2 ≤ (typedCoefficient+12003)*B^25 at b2
  have one := Nat.one_le_pow 25 B positive
  change t0+1+(t1+1+(t2+1+3)) ≤ (typedCoefficient+225000000)*B^25
  rw [Nat.add_mul] at b2 ⊢
  omega

end Counting.StackMachine.RealizabilityCheck
