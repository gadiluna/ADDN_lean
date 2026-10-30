import Counting.ExternalCoefficientEntry

namespace Counting.External.CoefficientMachine

theorem typedGeneratorCost_polynomial (input : X3CEncoding.Input) :
    typedGeneratorCost input ≤ 65536000000000000*((X3CEncoding.codec.encode input).length+1)^8 := by
  obtain ⟨universeBound,countBound⟩:=X3CEncoding.input_size_bounds input
  exact generatorCost_polynomial input _ (by omega) countBound

def entryCoefficient := CoverInputValidation.coefficient+65536000000000110+
  2*((Encoding.list Encoding.natural).encode []).length

theorem entryCost_polynomial (input : List Bool) : entryCost input ≤ entryCoefficient*(input.length+1)^8 := by
  let S:=input.length+1
  have positive : 1 ≤ S := by dsimp only [S];omega
  have powers : S^5 ≤ S^8 := Nat.pow_le_pow_right positive (by decide)
  have linear : S ≤ S^8 := Nat.le_self_pow (by decide) _
  have one : 1 ≤ S^8 := Nat.one_le_pow _ _ positive
  have len : input.length ≤ S := by dsimp only [S];omega
  have validationLimit : CoverInputValidation.coefficient*S^5 ≤ CoverInputValidation.coefficient*S^8 :=
    Nat.mul_le_mul_left _ powers
  by_cases valid : CoverInputValidation.validInput input=true
  · obtain ⟨typed,encoded⟩:=(CoverInputValidation.validInput_iff input).mp valid
    have decoded:=(X3CEncoding.codec.decodeExact_iff input typed).mpr encoded
    have generated:=typedGeneratorCost_polynomial typed
    rw [encoded] at generated
    change typedGeneratorCost typed ≤ 65536000000000000*S^8 at generated
    simp only [entryCost,valid,if_true,decoded]
    change CoverInputValidation.coefficient*S^5+10*input.length+100+
      2*((Encoding.list Encoding.natural).encode []).length+typedGeneratorCost typed ≤ entryCoefficient*S^8
    unfold entryCoefficient
    nlinarith only [validationLimit,linear,one,len,generated]
  · have invalid : CoverInputValidation.validInput input=false := Bool.eq_false_iff.mpr valid
    simp only [entryCost,invalid,Bool.false_eq_true,if_false,Nat.add_zero]
    change CoverInputValidation.coefficient*S^5+10*input.length+100+
      2*((Encoding.list Encoding.natural).encode []).length ≤ entryCoefficient*S^8
    unfold entryCoefficient
    nlinarith only [validationLimit,linear,one,len]

end Counting.External.CoefficientMachine
