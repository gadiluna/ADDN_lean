import Counting.NetworkRecognitionTotal
import Counting.MachineBooleanDecision

namespace Counting.StackMachine.NetworkRecognition

theorem totalNetworkExponent_eq : totalNetworkExponent=7 := by decide
theorem totalNetworkCoefficient_eq : totalNetworkCoefficient=70000132297 := by decide

/-- Explicit physical step bound after the verified stack-to-tape compiler,
including bootstrapping and the complete output-tape cleanup. -/
theorem networkValidationMachine_concrete : Complexity.ComputesCleanIn networkValidationMachine
    (fun input=>[validNetworkWord input])
    (Complexity.polynomial (20*(70000132326)^2) 16) := by
  simpa only [totalNetworkExponent_eq,totalNetworkCoefficient_eq] using networkValidationMachine_computes

def admissibleNetworkLanguage : Complexity.Language := {input | (Encoding.decodeNetwork? input).isSome=true}
def admissibleNetworkDecision : Machine.Program := Machine.compose networkValidationMachine Machine.booleanDecision
def admissibleNetworkCoefficient : Nat := Complexity.compositionCoefficient (20*(70000132326)^2) 1 0
def admissibleNetworkExponent : Nat := Complexity.compositionExponent 16 0

theorem admissibleNetworkDecision_decides : Complexity.DecidesIn admissibleNetworkDecision admissibleNetworkLanguage
    (Complexity.polynomial admissibleNetworkCoefficient admissibleNetworkExponent) := by
  have decision:=networkValidationMachine_concrete.boolean_decides
  refine ⟨decision.1,?_⟩
  intro input
  simpa only [validNetworkWord_eq_decodeNetwork,admissibleNetworkDecision,
    admissibleNetworkLanguage] using decision.2 input

/-- This checks the explicit network's syntax and admissibility. It does
not assert a runtime bound for computing its agents' final views. -/
theorem admissibleNetworkLanguage_in_P : Complexity.P admissibleNetworkLanguage :=
  ⟨admissibleNetworkDecision,admissibleNetworkCoefficient,admissibleNetworkExponent,admissibleNetworkDecision_decides⟩

end Counting.StackMachine.NetworkRecognition
