import Counting.HardnessNetworkMachineMachine
import Counting.HardnessNetworkMachineReductionSpec
import Counting.ExternalCoverVerifierMachine

namespace Counting.HardnessNetworkMachine

def normalizedNetworkMachine : Machine.Program :=
  Machine.compose External.CoverNormalization.machineGenerator networkMachine

def normalizedNetworkCoefficient := Complexity.compositionCoefficient
  (20*(External.CoverNormalization.entryCoefficient+67)^2)
  (20*(networkEntryCoefficient+99)^2) 20

def normalizedNetworkExponent := Complexity.compositionExponent 12 20

theorem normalizedNetworkMachine_computesCleanIn :
    Complexity.ComputesCleanIn normalizedNetworkMachine normalizedNetwork
      (Complexity.polynomial normalizedNetworkCoefficient normalizedNetworkExponent) :=
  External.CoverNormalization.machineGenerator_computesCleanIn.compose networkMachine_computesCleanIn

def SomeAgentKnowsLanguage : Complexity.Language := {word | Encoding.BinarySomeAgentKnows word}

/-- Polynomial many-one hardness uses the concrete normalization and
network machines, including every bitword outside the source grammar. -/
theorem complementX3C_reduces_SomeAgentKnows :
    Complexity.ManyOnePoly External.CoverMachine.X3CLanguageᶜ SomeAgentKnowsLanguage :=
  ⟨normalizedNetwork,normalizedNetworkMachine,normalizedNetworkCoefficient,normalizedNetworkExponent,
    normalizedNetworkMachine_computesCleanIn,fun word=>(normalizedNetwork_correct word).symm⟩

theorem SomeAgentKnows_coNPHard : Complexity.coNPHard SomeAgentKnowsLanguage :=
  External.CoverMachine.X3C_NPHard.complement.of_reduction complementX3C_reduces_SomeAgentKnows

end Counting.HardnessNetworkMachine
