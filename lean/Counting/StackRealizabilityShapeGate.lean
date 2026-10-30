import Counting.StackRealizabilityTypedBounds
import Counting.StackRealizabilityInputShape
import Counting.StackReadBranch

namespace Counting.StackMachine.RealizabilityCheck
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/-- A failed dimension/positivity check takes a constant-time rejecting
branch. Only a successful check enters the round verifier. -/
def shapeGate : Routine 98 := branchRead 85 typedCheck (skip 98)

theorem shapeGate_executes (vista : Executable.Vista) (values : List Nat) (ell order : Nat)
    (valid : vista.valid=true) :
    ∃ time ≤ Complexity.polynomial (typedCoefficient+3) 25
        (Encoding.verifierInput.encode (vista,values,ell,order)).length,
      ∃ result : Store 98,
        Executes shapeGate
          (inputCountStore vista values ell order [countsShapeCheck values.toArray vista.nodes.size]) time result ∧
        result 1=[] ∧ result 85=[countsShapeCheck values.toArray vista.nodes.size &&
          typedChecks vista values ell order] := by
  let input := inputCountStore vista values ell order [countsShapeCheck values.toArray vista.nodes.size]
  have flag : input 85=[countsShapeCheck values.toArray vista.nodes.size] := by simp [input,inputCountStore,inputNodesStore,inputFieldsStore]
  have one : 1 ≤ ((Encoding.verifierInput.encode (vista,values,ell,order)).length+1)^25 :=
    Nat.one_le_pow _ _ (by omega)
  cases shape : countsShapeCheck values.toArray vista.nodes.size with
  | false =>
    have selected : Executes (if false then typedCheck else skip 98) input 0 input := skip_executes input
    have branch := branchRead_executes (85:Fin 100) typedCheck (skip 98) false [] input input 0
      (by simpa only [shape] using flag) selected
    refine ⟨3,?_,input,?_,?_,?_⟩
    · unfold Complexity.polynomial;rw [Nat.add_mul];omega
    · simpa only [shapeGate,input,shape] using branch
    · simp [input,inputCountStore,inputNodesStore,inputFieldsStore]
    · simp [input,inputCountStore,inputNodesStore,inputFieldsStore,shape]
  | true =>
    have length : values.length=vista.nodes.size := by
      have := ((countsShapeCheck_iff values.toArray vista.nodes.size).mp shape).1
      simpa only [List.size_toArray] using this
    obtain ⟨time,bound,run⟩ := typedCheck_executes vista values ell order valid length true []
    have runtime := bound.trans (typedCheckCost_input_bound vista values ell order valid)
    simp only [Bool.true_and] at run
    let result := typedResultStore vista values ell order [typedChecks vista values ell order]
    have selected : Executes (if true then typedCheck else skip 98) input time result := by
      change Executes typedCheck input time result
      simpa only [input,shape,result] using run
    have branch := branchRead_executes (85:Fin 100) typedCheck (skip 98) true [] input result time
      (by simpa only [shape] using flag) selected
    refine ⟨time+3,?_,result,?_,?_,?_⟩
    · unfold Complexity.polynomial at runtime ⊢;rw [Nat.add_mul];omega
    · simpa only [shapeGate,input,shape] using branch
    · simp [result,typedResultStore,roundFile]
    · simp [result,typedResultStore,roundFile,roundInputData]

end Counting.StackMachine.RealizabilityCheck
