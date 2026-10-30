import Counting.StackRealizabilityMachineSpec
import Counting.MachineBooleanDecision

namespace Counting.StackMachine.RealizabilityCheck

def certificateLanguage : Complexity.Language := {input | encodedVerifier input=true}

def certificateDecision : Machine.Program :=
  Machine.compose certificateMachine Machine.booleanDecision

def certificateDecisionCoefficient : Nat :=
  Complexity.compositionCoefficient certificateMachineCoefficient 1 0

def certificateDecisionExponent : Nat := Complexity.compositionExponent 52 0

theorem certificateDecision_decides : Complexity.DecidesIn certificateDecision certificateLanguage
    (Complexity.polynomial certificateDecisionCoefficient certificateDecisionExponent) :=
  certificateMachine_computes.boolean_decides

/-- This is the language of certificate-input tuples. Existentially
quantifying certificates to obtain recognition languages requires the
separate witness-size and verifier-input assembly proofs. -/
theorem certificateLanguage_in_P : Complexity.P certificateLanguage :=
  ⟨certificateDecision,certificateDecisionCoefficient,certificateDecisionExponent,certificateDecision_decides⟩

end Counting.StackMachine.RealizabilityCheck
