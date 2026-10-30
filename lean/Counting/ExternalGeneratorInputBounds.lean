import Counting.ExternalGeneratorProgram

namespace Counting.External.CookLevin.StackGenerator
open InitialRows

theorem generatorDimensionSum_bound (input : List Bool) (witness time : Nat) :
    let width := MachineBridge.width (capacity input witness) time
    (time+1)*width+width+witness+1 ≤ 3*(width+1)^2 := by
  dsimp only
  let width := MachineBridge.width (capacity input witness) time
  have ht : time≤width := by dsimp [width,MachineBridge.width]; omega
  have hw : witness≤width := by dsimp [width,MachineBridge.width,capacity]; omega
  have product := Nat.mul_le_mul ht (Nat.le_refl width)
  change (time+1)*width+width+witness+1 ≤ 3*(width+1)^2
  nlinarith

theorem formulaBodyBound_input (program : Machine.Program) (input : List Bool) (witness time : Nat) :
    formulaBodyBound program time (MachineBridge.width (capacity input witness) time) witness ≤
      16*formulaBodyCoefficient program*(MachineBridge.width (capacity input witness) time+1)^8 := by
  let width := MachineBridge.width (capacity input witness) time
  have ht : time≤width := by dsimp [width,MachineBridge.width]; omega
  have product : (time+1)*(width+1)+1≤2*(width+1)^2 := by nlinarith
  have bounded := formulaBodyBound_polynomial program time (setup input witness time)
  have weighted := Nat.mul_le_mul_left (formulaBodyCoefficient program) (Nat.pow_le_pow_left product 4)
  apply bounded.trans
  change formulaBodyCoefficient program*((time+1)*(width+1)+1)^4 ≤ 16*formulaBodyCoefficient program*(width+1)^8
  simpa only [mul_pow,← pow_mul,show 2^4=16 by decide,show 2*4=8 by decide,
    Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc] using weighted

theorem generatorWidthPower_bound (coefficient exponent witnessCoefficient witnessExponent power : Nat) (input : List Bool) :
    let witness := Complexity.polynomial witnessCoefficient witnessExponent input.length
    let time := timeBound coefficient exponent input witness
    (MachineBridge.width (capacity input witness) time+1)^power ≤
      (widthCoefficient coefficient exponent witnessCoefficient)^power*
        (input.length+1)^(power*widthExponent exponent witnessExponent) := by
  have bound := Nat.pow_le_pow_left (reduction_width_bound coefficient exponent witnessCoefficient witnessExponent input) power
  simpa only [mul_pow,← pow_mul,Nat.mul_comm (widthExponent exponent witnessExponent) power] using bound

end Counting.External.CookLevin.StackGenerator
