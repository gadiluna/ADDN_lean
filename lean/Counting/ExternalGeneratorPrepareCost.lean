import Counting.ExternalGeneratorPrepare
import Counting.ExternalCookLevinSize

namespace Counting.External.CookLevin.StackGenerator
open StackMachine.Routine

theorem generatorPrepareCost_dimension_bound (input : List Bool)
    (coefficient exponent witnessCoefficient witnessExponent : Nat) :
    let witness := Complexity.polynomial witnessCoefficient witnessExponent input.length
    let time := timeBound coefficient exponent input witness
    let width := MachineBridge.width (capacity input witness) time
    generatorPrepareCost input coefficient exponent witnessCoefficient witnessExponent ≤
      boundsCost input.length coefficient exponent witnessCoefficient witnessExponent+60*(width+1)^2 := by
  dsimp only
  let witness := Complexity.polynomial witnessCoefficient witnessExponent input.length
  let time := timeBound coefficient exponent input witness
  let width := MachineBridge.width (capacity input witness) time
  have widthEq : width=2*input.length+1+witness+2*time+3 := by
    simp only [width,MachineBridge.width,capacity,Encoding.frame_length]
  have inputBound : input.length≤width := by omega
  have timeBound : time≤width := by omega
  have witnessBound : witness≤width := by omega
  change boundsCost input.length coefficient exponent witnessCoefficient witnessExponent+1+
    (5*time+4+1+(10*(time+1)+5*(2*(input.length+1)+witness)+9+1+
      (10*input.length+7+1+((5*width+9)*(time+1)+7)))) ≤ _
  change _ ≤ boundsCost input.length coefficient exponent witnessCoefficient witnessExponent+60*(width+1)^2
  have product := Nat.mul_le_mul_left (5*width+9) (show time+1≤width+1 by omega)
  nlinarith

def generatorPrepareCoefficient (coefficient exponent witnessCoefficient witnessExponent : Nat) :=
  boundsCoefficient coefficient exponent witnessCoefficient witnessExponent+
    60*(widthCoefficient coefficient exponent witnessCoefficient)^2

theorem generatorPrepareCost_polynomial (input : List Bool)
    (coefficient exponent witnessCoefficient witnessExponent : Nat) :
    generatorPrepareCost input coefficient exponent witnessCoefficient witnessExponent ≤
      Complexity.polynomial (generatorPrepareCoefficient coefficient exponent witnessCoefficient witnessExponent)
        (2*widthExponent exponent witnessExponent) input.length := by
  have first := boundsCost_polynomial input.length coefficient exponent witnessCoefficient witnessExponent
  have widths := reduction_width_bound coefficient exponent witnessCoefficient witnessExponent input
  have second := Nat.mul_le_mul_left 60 (Nat.pow_le_pow_left widths 2)
  have powered : (input.length+1)^(boundsExponent exponent witnessExponent)≤
      (input.length+1)^(2*widthExponent exponent witnessExponent) := by
    apply Nat.pow_le_pow_right (by omega)
    unfold boundsExponent widthExponent
    omega
  have firstBig := first.trans (Nat.mul_le_mul_left _ powered)
  have total := generatorPrepareCost_dimension_bound input coefficient exponent witnessCoefficient witnessExponent
  dsimp only at total second
  simp only [mul_pow,← pow_mul] at second
  have mulSwap : widthExponent exponent witnessExponent*2=2*widthExponent exponent witnessExponent := Nat.mul_comm _ _
  rw [mulSwap] at second
  unfold generatorPrepareCoefficient Complexity.polynomial
  nlinarith

end Counting.External.CookLevin.StackGenerator
