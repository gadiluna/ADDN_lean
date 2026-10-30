import Counting.ExternalCookLevinCounters

namespace Counting.External.CookLevin.StackGenerator
open StackMachine.Routine

def boundsCoefficient (coefficient exponent witnessCoefficient witnessExponent : Nat) : Nat :=
  polynomialLengthCoefficient witnessCoefficient witnessExponent+20+5*witnessCoefficient+
    (20*exponent*(coefficient+1)+2*coefficient+1)*(witnessCoefficient+3)^exponent

def boundsExponent (exponent witnessExponent : Nat) : Nat := (witnessExponent+1)*(exponent+1)

/-- Polynomial runtime of the executable preparation of both Cook–Levin
bounds. This is a stack-instruction bound, not an output-size argument. -/
theorem boundsCost_polynomial (length coefficient exponent witnessCoefficient witnessExponent : Nat) :
    boundsCost length coefficient exponent witnessCoefficient witnessExponent ≤
      Complexity.polynomial (boundsCoefficient coefficient exponent witnessCoefficient witnessExponent)
        (boundsExponent exponent witnessExponent) length := by
  let b := length+1
  have positive : 0 < b := by dsimp [b]; omega
  have basePower : b ≤ b^(witnessExponent+1) := by
    simpa only [pow_one] using Nat.pow_le_pow_right positive (show 1 ≤ witnessExponent+1 by omega)
  have witnessPower : b^witnessExponent ≤ b^(witnessExponent+1) := Nat.pow_le_pow_right positive (by omega)
  have onePower : 1 ≤ b^(witnessExponent+1) := Nat.one_le_pow _ _ positive
  have baseBound : 2*b+witnessCoefficient*b^witnessExponent+1 ≤
      (witnessCoefficient+3)*b^(witnessExponent+1) := by
    have weighted := Nat.mul_le_mul_left witnessCoefficient witnessPower
    nlinarith
  have powered := Nat.pow_le_pow_left baseBound exponent
  have monomialBound := monomialTime_bound (2*b+witnessCoefficient*b^witnessExponent) coefficient exponent
  have monomialScaled := Nat.mul_le_mul_left (20*exponent*(coefficient+1)+2*coefficient+1) powered
  have monomialSmall : monomialTime (2*b+witnessCoefficient*b^witnessExponent) coefficient exponent ≤
      ((20*exponent*(coefficient+1)+2*coefficient+1)*(witnessCoefficient+3)^exponent)*
        b^((witnessExponent+1)*exponent) := by
    exact monomialBound.trans (by simpa only [mul_pow,← pow_mul,Nat.mul_assoc] using monomialScaled)
  have firstPower : b^(witnessExponent+1) ≤ b^(boundsExponent exponent witnessExponent) := by
    apply Nat.pow_le_pow_right positive
    unfold boundsExponent
    nlinarith
  have secondPower : b^((witnessExponent+1)*exponent) ≤ b^(boundsExponent exponent witnessExponent) := by
    apply Nat.pow_le_pow_right positive
    unfold boundsExponent
    nlinarith
  have first := (polynomialLengthTime_bound length witnessCoefficient witnessExponent).trans
    (Nat.mul_le_mul_left (polynomialLengthCoefficient witnessCoefficient witnessExponent) firstPower)
  have second := monomialSmall.trans (Nat.mul_le_mul_left
    ((20*exponent*(coefficient+1)+2*coefficient+1)*(witnessCoefficient+3)^exponent) secondPower)
  have baseFinal := basePower.trans firstPower
  have witnessFinal := Nat.mul_le_mul_left witnessCoefficient (witnessPower.trans firstPower)
  have oneFinal := onePower.trans firstPower
  unfold boundsCost timeRoutineCost boundsCoefficient Complexity.polynomial
  change polynomialLengthTime length witnessCoefficient witnessExponent+1+
    (10*b+5*(witnessCoefficient*b^witnessExponent)+9+
      monomialTime (2*b+witnessCoefficient*b^witnessExponent) coefficient exponent) ≤ _
  dsimp only [b] at first second baseFinal witnessFinal oneFinal ⊢
  nlinarith

end Counting.External.CookLevin.StackGenerator
