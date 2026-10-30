import Counting.ExternalMatchingEntry
import Counting.ExternalMatchingGeneratorBounds

namespace Counting.External.MatchingMachine

theorem typedGeneratorCost_polynomial (input : CNFInput) (three : ∀ clause∈input.2,clause.length=3) :
    typedGeneratorCost input≤1000000000000*((CNFEncoding.codec.encode input).length+1)^9 := by
  obtain ⟨nBound,mBound,_widthBound⟩ := CNFEncoding.input_size_bounds input
  exact matchingGeneratorCost_polynomial _ _ _ _ nBound mBound (matchingRows_stream_length input three)

def entryCoefficient := MatchingValidation.coefficient+1000000000110+2*(ThreeDMEncoding.codec.encode rejectMatching).length

theorem entryCost_polynomial (input : List Bool) : entryCost input≤entryCoefficient*(input.length+1)^9 := by
  let S := input.length+1
  have pos : 1≤S := by dsimp [S];omega
  have powers : S^5≤S^9 := Nat.pow_le_pow_right pos (by decide)
  have validation : MatchingValidation.coefficient*S^5≤MatchingValidation.coefficient*S^9 := Nat.mul_le_mul_left _ powers
  have linear : S≤S^9 := Nat.le_self_pow (by decide) S
  have one : 1≤S^9 := Nat.one_le_pow _ _ pos
  have len : input.length≤S := by dsimp [S];omega
  by_cases valid : MatchingValidation.check input=true
  · obtain ⟨formula,encoded,three⟩ := (MatchingValidation.check_iff input).mp valid
    have decoded := (CNFEncoding.codec.decodeExact_iff input formula).mpr encoded
    have generated := typedGeneratorCost_polynomial formula three
    rw [encoded] at generated
    change typedGeneratorCost formula≤1000000000000*S^9 at generated
    simp only [entryCost,valid,if_true,decoded]
    change MatchingValidation.coefficient*S^5+10*input.length+100+2*(ThreeDMEncoding.codec.encode rejectMatching).length+
      typedGeneratorCost formula≤entryCoefficient*S^9
    dsimp only [entryCoefficient]
    nlinarith only [validation,linear,one,len,generated]
  · have rejected : MatchingValidation.check input=false := Bool.eq_false_iff.mpr valid
    simp only [entryCost,rejected,Bool.false_eq_true,if_false,Nat.add_zero]
    change MatchingValidation.coefficient*S^5+10*input.length+100+2*(ThreeDMEncoding.codec.encode rejectMatching).length≤entryCoefficient*S^9
    dsimp only [entryCoefficient]
    nlinarith only [validation,linear,one,len]

end Counting.External.MatchingMachine
