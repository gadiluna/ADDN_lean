import Counting.GaussianLinearSizes

namespace Counting.StackMachine.GaussianCalls
open GaussianNormalMatrix GaussianBits GaussianEquationCheck
set_option maxRecDepth 20000
set_option exponentiation.threshold 4000

def prefixPolynomialCoefficient : Nat :=
  5+54*(GaussianNormal.normalPolynomialCoefficient+4)+600+54*(solutionPolynomialCoefficient+103)+9
def successPolynomialCoefficient : Nat :=
  132*solutionPolynomialCoefficient+234+
    44*(1000000000000000*(6*solutionPolynomialCoefficient+39)^5+(6*solutionPolynomialCoefficient+41))
def linearPolynomialCoefficient : Nat := prefixPolynomialCoefficient+1+successPolynomialCoefficient+7
def linearPhysicalCoefficient : Nat := 20*(linearPolynomialCoefficient+59)^2

private theorem add_three_bounds (a b c A B C P : Nat)
    (ha : a≤ A*P) (hb : b≤ B*P) (hc : c≤ C*P) :
    a+b+c≤ (A+B+C)*P := by
  simpa only [Nat.add_mul] using Nat.add_le_add (Nat.add_le_add ha hb) hc

private theorem prefix_arithmetic (length normalLength C D E : Nat)
    (normalBound : normalLength≤ 100*(length+1)^3) (coefficient : D*101^100≤ E) :
    5*length+54*(C*(length+1)^6+length+3)+6*normalLength+
        54*(D*(normalLength+1)^100+normalLength+3)+9≤
      (5+54*(C+4)+600+54*(E+103)+9)*(length+1)^300 := by
  let power := (length+1)^300
  have positive : 1≤ power := Nat.one_le_pow' 300 length
  have linear : length≤ power := (Nat.le_add_right length 1).trans (Nat.le_self_pow (by decide:300≠0) _)
  have cube : (length+1)^3≤ power := Nat.pow_le_pow_right (by omega) (by omega)
  have sixth : (length+1)^6≤ power := Nat.pow_le_pow_right (by omega) (by omega)
  have small : 1≤ (length+1)^3 := Nat.one_le_pow' 3 length
  have hundred : (normalLength+1)^100≤ 101^100*power := by
    calc
      _≤ (101*(length+1)^3)^100 := Nat.pow_le_pow_left (by omega) 100
      _=_ := by rw [mul_pow,←pow_mul]
  have normalSize : normalLength≤ 100*power := normalBound.trans (Nat.mul_le_mul_left 100 cube)
  have normalInner : C*(length+1)^6+length+3≤ (C+4)*power := by
    exact add_three_bounds _ _ _ C 1 3 power (Nat.mul_le_mul_left C sixth)
      (by simpa only [Nat.one_mul] using linear) (Nat.mul_le_mul_left 3 positive)
  have normalTime : 54*(C*(length+1)^6+length+3)≤ (54*(C+4))*power := by
    simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left 54 normalInner
  have multiplied : D*(normalLength+1)^100≤ E*power := by
    calc
      _≤ D*(101^100*power) := Nat.mul_le_mul_left D hundred
      _=(D*101^100)*power := (Nat.mul_assoc _ _ _).symm
      _≤ E*power := Nat.mul_le_mul_right power coefficient
  have squareInner : D*(normalLength+1)^100+normalLength+3≤ (E+103)*power :=
    add_three_bounds _ _ _ E 100 3 power multiplied normalSize (Nat.mul_le_mul_left 3 positive)
  have squareTime : 54*(D*(normalLength+1)^100+normalLength+3)≤ (54*(E+103))*power := by
    simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left 54 squareInner
  have first : 5*length≤ 5*power := Nat.mul_le_mul_left 5 linear
  have third : 6*normalLength≤ 600*power := by
    simpa only [←Nat.mul_assoc] using Nat.mul_le_mul_left 6 normalSize
  have last : 9≤ 9*power := Nat.mul_le_mul_left 9 positive
  simpa only [Nat.add_mul] using
    Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add first normalTime) third) squareTime) last

theorem prefixCost_polynomial (length normalLength : Nat)
    (normalBound : normalLength≤ 100*(length+1)^3) :
    prefixCost length normalLength≤ prefixPolynomialCoefficient*(length+1)^300 := by
  apply prefix_arithmetic length normalLength _ _ _ normalBound
  exact Nat.mul_le_mul_right _ (Nat.le_add_right _ _)

theorem successCost_polynomial (width : Nat) (equations : List Executable.Equation) (solution : Fin width → Rat)
    (integral : ∀ row column,(augmented (Executable.normalSystem width equations) row column).den=1)
    (found : StoredGaussian.solve? (Executable.normalSystem width equations)=some solution) :
    successCost width equations solution≤ successPolynomialCoefficient*
      ((GaussianNormal.inputWord width (equationMatrix width equations)).length+1)^1500 := by
  let length := (GaussianNormal.inputWord width (equationMatrix width equations)).length
  let matrixLength := (Encoding.rationalMatrix.encode (equationMatrix width equations)).length
  let solutionLength := (Encoding.rationalRow.encode (List.ofFn solution)).length
  let vectorLength := (Encoding.rationalRow.encode (vector (List.ofFn solution))).length
  let checkerLength := (GaussianCheck.inputCodec.encode (vector (List.ofFn solution),equationMatrix width equations)).length
  let power := (length+1)^300
  let high := (length+1)^1500
  have inputLength : length=2*width+1+matrixLength := by
    simp [length,GaussianNormal.inputWord,Encoding.frame_length,matrixLength]
  have checkerLengthEq : checkerLength=2*vectorLength+1+matrixLength := by
    change (Encoding.frame (Encoding.rationalRow.encode (vector (List.ofFn solution)))++
      Encoding.rationalMatrix.encode (equationMatrix width equations)).length=_
    simp [Encoding.frame_length,vectorLength,matrixLength]
  have solutionBound := linearSolution_length_bound width equations integral solution found
  have vectorBound := vectorWord_length_bound (List.ofFn solution)
  change solutionLength≤ solutionPolynomialCoefficient*power at solutionBound
  change vectorLength≤ 3*solutionLength+18 at vectorBound
  have positive : 1≤ power := Nat.one_le_pow' 300 length
  have linear : length+1≤ power := Nat.le_self_pow (by decide:300≠0) _
  have raised : power≤ high := Nat.pow_le_pow_right (by omega) (by omega)
  have checkerBound : checkerLength+1≤ (6*solutionPolynomialCoefficient+39)*power := by
    generalize power=P at *
    nlinarith only [solutionBound,vectorBound,checkerLengthEq,inputLength,linear,positive]
  have checkerPower : (checkerLength+1)^5≤ (6*solutionPolynomialCoefficient+39)^5*high := by
    calc
      _≤ ((6*solutionPolynomialCoefficient+39)*power)^5 := Nat.pow_le_pow_left checkerBound 5
      _=_ := by dsimp only [power,high];rw [mul_pow,←pow_mul]
  have checkTime : checkCost checkerLength≤ 44*(1000000000000000*(6*solutionPolynomialCoefficient+39)^5+(6*solutionPolynomialCoefficient+41))*high := by
    have extra : checkerLength+3≤ (6*solutionPolynomialCoefficient+41)*power := by
      generalize power=P at *
      nlinarith only [checkerBound,positive]
    have extraHigh := Nat.mul_le_mul_left (6*solutionPolynomialCoefficient+41) raised
    unfold checkCost
    generalize power=P at *
    generalize high=H at *
    generalize (checkerLength+1)^5=F at *
    nlinarith only [extra,extraHigh,checkerPower]
  have rest : 17*solutionLength+100*(solutionLength+1)+6*width+6*matrixLength+5*vectorLength+32≤ (132*solutionPolynomialCoefficient+234)*power := by
    generalize power=P at *
    nlinarith only [solutionBound,vectorBound,inputLength,linear,positive]
  have restHigh := Nat.mul_le_mul_left (132*solutionPolynomialCoefficient+234) raised
  change successCost width equations solution≤ successPolynomialCoefficient*high
  change 11*solutionLength+100*(solutionLength+1)+6*width+6*matrixLength+5*vectorLength+
    checkCost checkerLength+24+6*solutionLength+8≤ successPolynomialCoefficient*high
  unfold successPolynomialCoefficient
  generalize power=P at *
  generalize high=H at *
  nlinarith only [rest,restHigh,checkTime]

theorem linearCost_polynomial (width : Nat) (equations : List Executable.Equation)
    (integral : ∀ row column,(augmented (Executable.normalSystem width equations) row column).den=1) :
    linearCost width equations≤ linearPolynomialCoefficient*
      ((GaussianNormal.inputWord width (equationMatrix width equations)).length+1)^1500 := by
  let length := (GaussianNormal.inputWord width (equationMatrix width equations)).length
  have before := prefixCost_polynomial length
    (Encoding.rationalMatrix.encode (StoredGaussian.augmentedMatrix (Executable.normalSystem width equations))).length
    (normalWord_length_bound width equations)
  have raised : (length+1)^300≤ (length+1)^1500 := Nat.pow_le_pow_right (by omega) (by omega)
  have beforeHigh := Nat.mul_le_mul_left prefixPolynomialCoefficient raised
  have positive := Nat.one_le_pow' 1500 length
  have linear := Nat.le_self_pow (by decide:1500≠0) (length+1)
  have after : handleCost width equations≤ (successPolynomialCoefficient+7)*(length+1)^1500 := by
    cases found : StoredGaussian.solve? (Executable.normalSystem width equations) with
    | none =>
      simp only [handleCost,found]
      change length+6≤ _
      generalize (length+1)^1500=P at *
      nlinarith only [positive,linear]
    | some solution =>
      have bounded := successCost_polynomial width equations solution integral found
      simp only [handleCost,found]
      change successCost width equations solution≤ successPolynomialCoefficient*(length+1)^1500 at bounded
      generalize (length+1)^1500=P at *
      nlinarith only [bounded,positive]
  change linearCost width equations≤ linearPolynomialCoefficient*(length+1)^1500
  dsimp only [linearCost,linearPolynomialCoefficient]
  generalize (length+1)^300=P at *
  generalize (length+1)^1500=H at *
  nlinarith only [before,beforeHigh,after,positive]

end Counting.StackMachine.GaussianCalls
