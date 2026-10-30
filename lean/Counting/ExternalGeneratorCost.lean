import Counting.ExternalGeneratorInputBounds
import Counting.ExternalGeneratorCountBounds

namespace Counting.External.CookLevin.StackGenerator

def generatorDimensionCoefficient (program : Machine.Program) :=
  3*generatorCountCoefficient program+9*generatorHeaderCoefficient program+
    16*formulaBodyCoefficient program+3

def generatorCoefficient (program : Machine.Program)
    (coefficient exponent witnessCoefficient witnessExponent : Nat) :=
  generatorPrepareCoefficient coefficient exponent witnessCoefficient witnessExponent+
    generatorDimensionCoefficient program*(widthCoefficient coefficient exponent witnessCoefficient)^8

def generatorExponent (exponent witnessExponent : Nat) := 8*widthExponent exponent witnessExponent

theorem generatorCost_polynomial (program : Machine.Program) (input : List Bool)
    (coefficient exponent witnessCoefficient witnessExponent : Nat) :
    generatorCost program input coefficient exponent witnessCoefficient witnessExponent ≤
      Complexity.polynomial (generatorCoefficient program coefficient exponent witnessCoefficient witnessExponent)
        (generatorExponent exponent witnessExponent) input.length := by
  let witness := Complexity.polynomial witnessCoefficient witnessExponent input.length
  let time := timeBound coefficient exponent input witness
  let width := MachineBridge.width (capacity input witness) time
  let cells := (time+1)*width
  let size := cells+width+witness+1
  have dimension : size≤3*(width+1)^2 := generatorDimensionSum_bound input witness time
  have counts := generatorCountsCost_le program cells width witness
  have counted := counts.trans (Nat.mul_le_mul_left (generatorCountCoefficient program) dimension)
  have headers := formulaHeadersBound_le program cells width witness
  have headerPower := Nat.pow_le_pow_left dimension 2
  have headed := headers.trans (Nat.mul_le_mul_left (generatorHeaderCoefficient program) headerPower)
  simp only [mul_pow,←pow_mul,show 3^2=9 by decide,show 2*2=4 by decide] at headed
  have body : formulaBodyBound program time width witness ≤ 16*formulaBodyCoefficient program*(width+1)^8 :=
    formulaBodyBound_input program input witness time
  have power2 : (width+1)^2≤(width+1)^8 := Nat.pow_le_pow_right (by omega) (by decide)
  have power4 : (width+1)^4≤(width+1)^8 := Nat.pow_le_pow_right (by omega) (by decide)
  have countBig := Nat.mul_le_mul_left (3*generatorCountCoefficient program) power2
  have headerBig := Nat.mul_le_mul_left (9*generatorHeaderCoefficient program) power4
  have positive : 1≤(width+1)^8 := Nat.one_le_pow _ _ (by omega)
  have rest : generatorCountsCost program cells width witness+formulaBodyBound program time width witness+
      formulaHeadersBound (cells*Cellular.alphabet program) (formulaClauseCount program cells width witness)+3 ≤
        generatorDimensionCoefficient program*(width+1)^8 := by
    unfold generatorDimensionCoefficient
    nlinarith
  have widths := generatorWidthPower_bound coefficient exponent witnessCoefficient witnessExponent 8 input
  change (width+1)^8 ≤ (widthCoefficient coefficient exponent witnessCoefficient)^8*
    (input.length+1)^(8*widthExponent exponent witnessExponent) at widths
  have restBig := rest.trans (Nat.mul_le_mul_left (generatorDimensionCoefficient program) widths)
  have prepare := generatorPrepareCost_polynomial input coefficient exponent witnessCoefficient witnessExponent
  have preparePower : (input.length+1)^(2*widthExponent exponent witnessExponent) ≤
      (input.length+1)^(8*widthExponent exponent witnessExponent) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have prepareBig := prepare.trans (Nat.mul_le_mul_left
    (generatorPrepareCoefficient coefficient exponent witnessCoefficient witnessExponent) preparePower)
  change generatorPrepareCost input coefficient exponent witnessCoefficient witnessExponent+1+
    (generatorCountsCost program cells width witness+1+(formulaBodyBound program time width witness+1+
      formulaHeadersBound (cells*Cellular.alphabet program) (formulaClauseCount program cells width witness))) ≤ _
  unfold Complexity.polynomial generatorCoefficient generatorExponent
  nlinarith

end Counting.External.CookLevin.StackGenerator
