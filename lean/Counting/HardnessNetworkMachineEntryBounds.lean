import Counting.HardnessNetworkMachineEntry
import Counting.HardnessNetworkMachineGeneratorBounds

namespace Counting.HardnessNetworkMachine

def networkEntryCoefficient := External.CoverInputValidation.coefficient+100000000000000110

theorem networkEntryCost_polynomial (input : List Bool) :
    networkEntryCost input ≤ networkEntryCoefficient*(input.length+1)^9 := by
  let S:=input.length+1
  have positive : 1 ≤ S := by dsimp only [S];omega
  have powers : S^5 ≤ S^9 := Nat.pow_le_pow_right positive (by decide)
  have linear : S ≤ S^9 := Nat.le_self_pow (by decide) _
  have one : 1 ≤ S^9 := Nat.one_le_pow _ _ positive
  have len : input.length ≤ S := by dsimp only [S];omega
  have validationLimit : External.CoverInputValidation.coefficient*S^5 ≤
      External.CoverInputValidation.coefficient*S^9 := Nat.mul_le_mul_left _ powers
  by_cases valid : External.CoverInputValidation.validInput input=true
  · obtain ⟨typed,encoded⟩:=(External.CoverInputValidation.validInput_iff input).mp valid
    have decoded:=(X3CEncoding.codec.decodeExact_iff input typed).mpr encoded
    have generated:=networkGeneratorCost_polynomial typed
    rw [encoded] at generated
    change networkGeneratorCost typed ≤ 100000000000000000*S^9 at generated
    simp only [networkEntryCost,valid,if_true,decoded]
    change External.CoverInputValidation.coefficient*S^5+10*input.length+100+
      networkGeneratorCost typed ≤ networkEntryCoefficient*S^9
    unfold networkEntryCoefficient
    nlinarith only [validationLimit,linear,one,len,generated]
  · have invalid : External.CoverInputValidation.validInput input=false := Bool.eq_false_iff.mpr valid
    simp only [networkEntryCost,invalid,Bool.false_eq_true,if_false,Nat.add_zero]
    change External.CoverInputValidation.coefficient*S^5+10*input.length+100 ≤ networkEntryCoefficient*S^9
    unfold networkEntryCoefficient
    nlinarith only [validationLimit,linear,one,len]

end Counting.HardnessNetworkMachine
