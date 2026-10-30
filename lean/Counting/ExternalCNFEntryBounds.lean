import Counting.ExternalCNFEntry
import Counting.ExternalCNFGeneratorBounds

namespace Counting.External.CNFMachine

theorem typedGeneratorCost_polynomial (input : CNFInput) :
    typedGeneratorCost input ≤ 1000000000*((CNFEncoding.codec.encode input).length+1)^7 := by
  obtain ⟨nBound,mBound,widthBound⟩ := CNFEncoding.input_size_bounds input
  apply formulaGeneratorCost_polynomial _ _ _ _ _ nBound mBound widthBound
  exact generatedStream_length input

def entryCoefficient := validateCoefficient+1000000110+2*(CNFEncoding.codec.encode rejectFormula).length

theorem entryCost_polynomial (input : List Bool) : entryCost input ≤ entryCoefficient*(input.length+1)^7 := by
  let S := input.length+1
  have pos : 1 ≤ S := by dsimp [S];omega
  have powers : S^5 ≤ S^7 := Nat.pow_le_pow_right pos (by decide)
  have validation : validateCoefficient*S^5 ≤ validateCoefficient*S^7 := Nat.mul_le_mul_left _ powers
  have linear : S ≤ S^7 := Nat.le_self_pow (by decide) S
  have one : 1 ≤ S^7 := Nat.one_le_pow _ _ pos
  cases decoded : CNFEncoding.codec.decodeExact input with
  | none =>
    simp only [entryCost,decoded,Nat.add_zero]
    change validateCoefficient*S^5+10*input.length+100+2*(CNFEncoding.codec.encode rejectFormula).length ≤ entryCoefficient*S^7
    dsimp only [entryCoefficient]
    have len : input.length ≤ S := by dsimp [S];omega
    nlinarith only [validation,linear,one,len]
  | some formula =>
    have encoded := (CNFEncoding.codec.decodeExact_iff input formula).mp decoded
    have generated := typedGeneratorCost_polynomial formula
    rw [encoded] at generated
    change typedGeneratorCost formula ≤ 1000000000*S^7 at generated
    simp only [entryCost,decoded]
    change validateCoefficient*S^5+10*input.length+100+2*(CNFEncoding.codec.encode rejectFormula).length+typedGeneratorCost formula ≤ entryCoefficient*S^7
    dsimp only [entryCoefficient]
    have len : input.length ≤ S := by dsimp [S];omega
    nlinarith only [validation,linear,one,len,generated]

end Counting.External.CNFMachine
