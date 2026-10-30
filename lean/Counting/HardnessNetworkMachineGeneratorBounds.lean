import Counting.HardnessNetworkMachineGenerator
import Counting.HardnessNetworkMachineBuildBounds
import Counting.ExternalCoefficientBounds

namespace Counting.HardnessNetworkMachine

/-- Cost of coefficient generation, the paid workspace transfer and the
complete network constructor, in the actual canonical source length. -/
theorem networkGeneratorCost_polynomial (input : X3CEncoding.Input) :
    networkGeneratorCost input ≤ 100000000000000000*((X3CEncoding.codec.encode input).length+1)^9 := by
  let L:=(X3CEncoding.codec.encode input).length
  obtain ⟨universeBound,countBound⟩:=X3CEncoding.input_size_bounds input
  have qBound : input.1 ≤ L := by dsimp only [L];omega
  have count : input.2.1 ≤ L := countBound
  have coefficient:=External.CoefficientMachine.generatorCost_polynomial input L qBound count
  have copying:=External.CoefficientMachine.inputCoefficients_encoding_length input L qBound count
  have construction:=buildNetworkCost_polynomial_shifted input L qBound count
  have shifted : L+4 ≤ 4*(L+1) := by omega
  have copyBound : ((Encoding.list Encoding.natural).encode
      (External.CoefficientMachine.inputCoefficients input)).length ≤ 1280*(L+1)^3 := by
    apply copying.trans
    calc
      20*(L+4)^3 ≤ 20*(4*(L+1))^3 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left shifted _)
      _ = _ := by ring
  have p3 : (L+1)^3 ≤ (L+1)^9 := Nat.pow_le_pow_right (by omega) (by decide)
  have p8 : (L+1)^8 ≤ (L+1)^9 := Nat.pow_le_pow_right (by omega) (by decide)
  have one : 1 ≤ (L+1)^9 := Nat.one_le_pow _ _ (by omega)
  change External.CoefficientMachine.generatorCost L input.1 input.2.1
    ((Encoding.list Encoding.natural).encode (External.CoefficientMachine.inputCoefficients input)).length+
    6*((Encoding.list Encoding.natural).encode (External.CoefficientMachine.inputCoefficients input)).length+
    buildNetworkCost input.1 (External.CoefficientMachine.inputCoefficients input)+8 ≤
    100000000000000000*(L+1)^9
  nlinarith only [coefficient,construction,copyBound,p3,p8,one]

end Counting.HardnessNetworkMachine
