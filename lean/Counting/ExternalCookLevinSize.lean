import Counting.ExternalCookLevin

namespace Counting.External.InitialRows
open Machine Cellular

def sizeCoefficient (program : Program) : ℕ :=
  let d := alphabet program
  2*d+(1+d*d)*(d+2)+12*d^4+1

theorem Setup.sizeBound_le {width : ℕ} (setup : Setup width) (program : Program) (time bound : ℕ)
    (widthBound : width ≤ bound) (witnessBound : setup.capacity ≤ bound) (timeBound : time ≤ bound) :
    setup.sizeBound program time ≤ sizeCoefficient program*(bound+1)^2 := by
  have nBound : (time+1)*width ≤ (bound+1)^2 := by
    simpa only [pow_two] using Nat.mul_le_mul (by omega : time+1 ≤ bound+1)
      (by omega : width ≤ bound+1)
  have witnessSquare := Nat.mul_le_mul witnessBound witnessBound
  have transitionBound := Nat.mul_le_mul timeBound widthBound
  have mBound : width+setup.capacity*setup.capacity+time*width ≤ 3*(bound+1)^2 := by nlinarith
  have wBound : width ≤ (bound+1)^2 := by nlinarith
  have oneBound : 1 ≤ (bound+1)^2 := by nlinarith
  have first := Nat.mul_le_mul_right (alphabet program) nBound
  have second := Nat.mul_le_mul_right (alphabet program+2)
    (Nat.mul_le_mul_right (1+alphabet program*alphabet program) nBound)
  have third := Nat.mul_le_mul_right ((alphabet program)^4*4) mBound
  have fourth := Nat.mul_le_mul_right (alphabet program) wBound
  unfold Setup.sizeBound sizeCoefficient
  nlinarith

def binaryCoefficient (program : Program) : ℕ :=
  2*(sizeCoefficient program)^2+10*sizeCoefficient program+2

theorem Setup.formula_binary_polynomial {width : ℕ} (setup : Setup width) (program : Program)
    (rotation : Equiv.Perm (Fin width)) (time bound : ℕ)
    (widthBound : width ≤ bound) (witnessBound : setup.capacity ≤ bound) (timeBound : time ≤ bound) :
    (CNFEncoding.codec.encode ⟨((time+1)*width)*alphabet program,
      setup.formula program rotation time⟩).length ≤ binaryCoefficient program*(bound+1)^4 := by
  have small := setup.sizeBound_le program time bound widthBound witnessBound timeBound
  have binary := setup.formula_binary_length program rotation time
  have squared := Nat.pow_le_pow_left small 2
  have base : (bound+1)^2 ≤ (bound+1)^4 := by nlinarith [sq_nonneg (bound:ℤ)]
  have weighted := Nat.mul_le_mul_left (10*sizeCoefficient program) base
  have positive : 1 ≤ (bound+1)^4 := Nat.pow_pos (by omega)
  unfold binaryCoefficient
  nlinarith

end Counting.External.InitialRows

namespace Counting.External.CookLevin
open Machine InitialRows MachineBridge

theorem boundedInput_binary_polynomial (program : Program) (input : List Bool) (witnessBound time : ℕ) :
    (CNFEncoding.codec.encode (boundedInput program input witnessBound time)).length ≤
      binaryCoefficient program * (width (capacity input witnessBound) time+1)^4 := by
  exact (setup input witnessBound time).formula_binary_polynomial program _ time _ le_rfl
    (by change witnessBound ≤ width (capacity input witnessBound) time; unfold width capacity; omega)
    (by unfold width; omega)

def widthCoefficient (coefficient exponent witnessCoefficient : ℕ) : ℕ :=
  witnessCoefficient+7+2*coefficient*(witnessCoefficient+4)^exponent

def widthExponent (exponent witnessExponent : ℕ) : ℕ :=
  (witnessExponent+1)*(exponent+1)

theorem reduction_width_bound (coefficient exponent witnessCoefficient witnessExponent : ℕ)
    (input : List Bool) :
    let W := Complexity.polynomial witnessCoefficient witnessExponent input.length
    width (capacity input W) (timeBound coefficient exponent input W)+1 ≤
      widthCoefficient coefficient exponent witnessCoefficient *
        (input.length+1)^(widthExponent exponent witnessExponent) := by
  dsimp only
  let b := input.length+1
  have positive : 0 < b := by dsimp [b]; omega
  have basePower : b ≤ b^(witnessExponent+1) := by
    simpa only [pow_one] using Nat.pow_le_pow_right positive (show 1 ≤ witnessExponent+1 by omega)
  have witnessPower : b^witnessExponent ≤ b^(witnessExponent+1) :=
    Nat.pow_le_pow_right positive (by omega)
  have onePower : 1 ≤ b^(witnessExponent+1) := by
    have : 0 < b^(witnessExponent+1) := Nat.pow_pos positive
    omega
  have cap : capacity input (Complexity.polynomial witnessCoefficient witnessExponent input.length) ≤
      (witnessCoefficient+3)*b^(witnessExponent+1) := by
    unfold capacity Complexity.polynomial
    rw [Encoding.frame_length]
    change 2*input.length+1+witnessCoefficient*b^witnessExponent ≤ _
    have weighted := Nat.mul_le_mul_left witnessCoefficient witnessPower
    have bEq : b = input.length+1 := rfl
    nlinarith
  have capOne : capacity input (Complexity.polynomial witnessCoefficient witnessExponent input.length)+1 ≤
      (witnessCoefficient+4)*b^(witnessExponent+1) := by nlinarith
  have time : timeBound coefficient exponent input
      (Complexity.polynomial witnessCoefficient witnessExponent input.length) ≤
      (coefficient*(witnessCoefficient+4)^exponent)*b^((witnessExponent+1)*exponent) := by
    have powers := Nat.mul_le_mul_left coefficient (Nat.pow_le_pow_left capOne exponent)
    simpa only [timeBound, Complexity.polynomial, mul_pow, ← pow_mul, Nat.mul_assoc] using powers
  have firstPower : b^(witnessExponent+1) ≤ b^(widthExponent exponent witnessExponent) := by
    apply Nat.pow_le_pow_right positive
    unfold widthExponent
    nlinarith
  have secondPower : b^((witnessExponent+1)*exponent) ≤ b^(widthExponent exponent witnessExponent) := by
    apply Nat.pow_le_pow_right positive
    unfold widthExponent
    nlinarith
  have finalPositive : 1 ≤ b^(widthExponent exponent witnessExponent) := by
    have : 0 < b^(widthExponent exponent witnessExponent) := Nat.pow_pos positive
    omega
  have capFinal := cap.trans (Nat.mul_le_mul_left (witnessCoefficient+3) firstPower)
  have timeFinal := time.trans (Nat.mul_le_mul_left (coefficient*(witnessCoefficient+4)^exponent) secondPower)
  unfold width widthCoefficient
  change _ ≤ (witnessCoefficient+7+2*coefficient*(witnessCoefficient+4)^exponent)*b^_
  nlinarith

/-- The generated *binary word*, including its explicit variable table,
has a standard polynomial length bound in the original input length. -/
theorem reduce_length_polynomial (program : Program) (coefficient exponent witnessCoefficient witnessExponent : ℕ)
    (input : List Bool) :
    (reduce program coefficient exponent witnessCoefficient witnessExponent input).length ≤
      Complexity.polynomial
        (binaryCoefficient program*(widthCoefficient coefficient exponent witnessCoefficient)^4)
        (4*widthExponent exponent witnessExponent) input.length := by
  have bounded := boundedInput_binary_polynomial program input
    (Complexity.polynomial witnessCoefficient witnessExponent input.length)
    (timeBound coefficient exponent input (Complexity.polynomial witnessCoefficient witnessExponent input.length))
  have widths := reduction_width_bound coefficient exponent witnessCoefficient witnessExponent input
  have powers := Nat.mul_le_mul_left (binaryCoefficient program) (Nat.pow_le_pow_left widths 4)
  unfold reduce reduceInput
  apply bounded.trans
  simpa only [Complexity.polynomial, mul_pow, ← pow_mul, Nat.mul_assoc, Nat.mul_comm 4] using powers

end Counting.External.CookLevin
