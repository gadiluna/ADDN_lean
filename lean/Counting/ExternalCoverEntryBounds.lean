import Counting.ExternalCoverEntry

namespace Counting.External.CoverMachine

theorem typedGeneratorCost_polynomial (input : ThreeDMEncoding.Input) :
    typedGeneratorCost input≤100000*((ThreeDMEncoding.codec.encode input).length+1)^4 := by
  obtain ⟨qBound,mBound⟩ := ThreeDMEncoding.input_size_bounds input
  exact coverGeneratorCost_polynomial _ _ _ _ qBound mBound (shiftedRows_stream_length input)

def entryCoefficient := MatchingInputValidation.coefficient+100110+2*(X3CEncoding.codec.encode rejectCover).length

theorem entryCost_polynomial (input : List Bool) : entryCost input≤entryCoefficient*(input.length+1)^5 := by
  let S := input.length+1
  have pos : 1≤S := by dsimp [S];omega
  have powers : S^4≤S^5 := Nat.pow_le_pow_right pos (by decide)
  have linear : S≤S^5 := Nat.le_self_pow (by decide) S
  have one : 1≤S^5 := Nat.one_le_pow _ _ pos
  have len : input.length≤S := by dsimp [S];omega
  by_cases valid : MatchingInputValidation.validInput input=true
  · obtain ⟨matching,encoded⟩ := (MatchingInputValidation.validInput_iff input).mp valid
    have decoded := (ThreeDMEncoding.codec.decodeExact_iff input matching).mpr encoded
    have generated := typedGeneratorCost_polynomial matching
    rw [encoded] at generated
    change typedGeneratorCost matching≤100000*S^4 at generated
    simp only [entryCost,valid,if_true,decoded]
    change MatchingInputValidation.coefficient*S^5+10*input.length+100+2*(X3CEncoding.codec.encode rejectCover).length+
      typedGeneratorCost matching≤entryCoefficient*S^5
    dsimp only [entryCoefficient]
    nlinarith only [linear,one,len,generated,powers]
  · have rejected : MatchingInputValidation.validInput input=false := Bool.eq_false_iff.mpr valid
    simp only [entryCost,rejected,Bool.false_eq_true,if_false,Nat.add_zero]
    change MatchingInputValidation.coefficient*S^5+10*input.length+100+2*(X3CEncoding.codec.encode rejectCover).length≤entryCoefficient*S^5
    dsimp only [entryCoefficient]
    nlinarith only [linear,one,len]

end Counting.External.CoverMachine
