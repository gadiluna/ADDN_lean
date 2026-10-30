import Counting.MachineNetworkComplement
import Counting.HardnessNetworkMachineReduction
import Counting.ComplexityInclusions

namespace Counting.NetworkComplement
open Complexity HardnessNetworkMachine

/-- Membership and hardness for the exact binary network language are both
realized by verified finite-alphabet polynomial-time machines. -/
theorem SomeAgentKnows_coNPComplete : coNPComplete SomeAgentKnowsLanguage :=
  ⟨StackMachine.NetworkComplement.BinarySomeAgentKnows_in_coNP,SomeAgentKnows_coNPHard⟩

/-- The hardness reductions always emit admissible loopless networks with
exactly one leader, including on malformed source words. -/
theorem SomeAgentKnows_one_leader_loopless_hard (source : Language) (member : coNP source) :
    ∃ f program coefficient exponent,
      ComputesCleanIn program f (polynomial coefficient exponent) ∧
      (∀ word,word∈source ↔ Encoding.BinarySomeAgentKnows (f word)) ∧
      ∀ word,∃ target,Encoding.decodeNetwork? (f word)=some target ∧
        Encoding.inputLeaderCount target=1 ∧
        ∀ r,0<r → r≤target.rounds.size → ∀agent:Encoding.InputAgent target,
          Encoding.inputGraph target r agent agent=0 := by
  obtain ⟨f,program,c,k,computes,correct⟩ := External.CoverMachine.X3C_NPHard.complement source member
  refine ⟨normalizedNetwork ∘ f,Machine.compose program normalizedNetworkMachine,
    compositionCoefficient c normalizedNetworkCoefficient normalizedNetworkExponent,
    compositionExponent k normalizedNetworkExponent,computes.compose normalizedNetworkMachine_computesCleanIn,?_,?_⟩
  · intro word
    exact (correct word).trans (normalizedNetwork_correct (f word)).symm
  · intro word
    exact normalizedNetwork_restricted (f word)

theorem SomeAgentKnows_not_P (separation : PNeNP) : ¬ P SomeAgentKnowsLanguage :=
  SomeAgentKnows_coNPHard.not_P separation

end Counting.NetworkComplement
