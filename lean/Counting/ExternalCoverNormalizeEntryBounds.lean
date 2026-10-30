import Counting.ExternalCoverNormalizeEntry

namespace Counting.External.CoverNormalization

theorem typedGeneratorCost_polynomial (input : X3CEncoding.Input) :
    typedGeneratorCost input≤100000*((X3CEncoding.codec.encode input).length+1)^3 := by
  simpa only [typedGeneratorCost,CoverInputValidation.inputRaw_encode] using
    generatorCost_polynomial (CoverInputValidation.inputRaw input)

def entryCoefficient := CoverInputValidation.coefficient+100110+2*(rejectedOutput).length

theorem entryCost_polynomial (input : List Bool) : entryCost input≤entryCoefficient*(input.length+1)^5 := by
  let S := input.length+1
  have pos : 1≤S := by dsimp [S];omega
  have powers : S^3≤S^5 := Nat.pow_le_pow_right pos (by decide)
  have linear : S≤S^5 := Nat.le_self_pow (by decide) S
  have one : 1≤S^5 := Nat.one_le_pow _ _ pos
  have len : input.length≤S := by dsimp [S];omega
  by_cases valid : CoverInputValidation.validInput input=true
  · obtain ⟨matching,encoded⟩ := (CoverInputValidation.validInput_iff input).mp valid
    have decoded := (X3CEncoding.codec.decodeExact_iff input matching).mpr encoded
    have generated := typedGeneratorCost_polynomial matching
    rw [encoded] at generated
    change typedGeneratorCost matching≤100000*S^3 at generated
    simp only [entryCost,valid,if_true,decoded]
    change CoverInputValidation.coefficient*S^5+10*input.length+100+2*(rejectedOutput).length+
      typedGeneratorCost matching≤entryCoefficient*S^5
    dsimp only [entryCoefficient]
    nlinarith only [linear,one,len,generated,powers]
  · have rejected : CoverInputValidation.validInput input=false := Bool.eq_false_iff.mpr valid
    simp only [entryCost,rejected,Bool.false_eq_true,if_false,Nat.add_zero]
    change CoverInputValidation.coefficient*S^5+10*input.length+100+2*(rejectedOutput).length≤entryCoefficient*S^5
    dsimp only [entryCoefficient]
    nlinarith only [linear,one,len]

end Counting.External.CoverNormalization
