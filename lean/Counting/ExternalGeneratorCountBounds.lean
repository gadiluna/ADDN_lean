import Counting.ExternalGeneratorCounts
import Counting.ExternalGeneratorHeaders

namespace Counting.External.CookLevin.StackGenerator
open StackMachine.Routine

def generatorCountCoefficient (program : Machine.Program) :=
  100*((oneHotTemplate (Cellular.alphabet program)).length+Cellular.alphabet program+
    (initialBinaryTemplate program).length+transitionClauseCount program+1)

theorem differenceCost_linear (first second coefficient size : Nat)
    (hf : first≤size) (hs : second≤size) (positive : 1≤size) :
    addScaledDifferenceCost first second coefficient ≤ (23+8*coefficient)*size := by
  have bound := addScaledDifferenceCost_le first second coefficient
  have a := Nat.mul_le_mul_left (6+5*coefficient) hf
  have b := Nat.mul_le_mul_left 7 hs
  have c := Nat.mul_le_mul_left (3*coefficient+10) positive
  nlinarith

theorem generatorCountsCost_le (program : Machine.Program) (cells width capacity : Nat) :
    generatorCountsCost program cells width capacity ≤
      generatorCountCoefficient program*(cells+width+capacity+1) := by
  let size := cells+width+capacity+1
  let a := Cellular.alphabet program
  let h := (oneHotTemplate a).length
  let b := (initialBinaryTemplate program).length
  let d := transitionClauseCount program
  have positive : 1≤size := by dsimp [size]; omega
  have hc : cells≤size := by dsimp [size]; omega
  have hw : width≤size := by dsimp [size]; omega
  have hk : capacity≤size := by dsimp [size]; omega
  have first := Nat.mul_le_mul_left h (show 5*cells+3≤8*size by omega)
  have second := Nat.mul_le_mul (Nat.sub_le a 3) (show 5*capacity+3≤8*size by omega)
  have third := differenceCost_linear width capacity (a-1) size hw hk positive
  have fourth := differenceCost_linear capacity 1 b size hk positive positive
  have fifth := differenceCost_linear cells width d size hc hw positive
  have sixth := Nat.mul_le_mul_left a (show 5*cells+3≤8*size by omega)
  have ordinary := Nat.mul_le_mul_left (8*size) (Nat.sub_le a 1)
  change generatorCountCoreCost program cells width capacity+8+a*(5*cells+3) ≤ 100*(h+a+b+d+1)*size
  unfold generatorCountCoreCost
  change h*(5*cells+3)+1+((a-3)*(5*capacity+3)+1+
    (addScaledDifferenceCost width capacity (a-1)+1+
      (addScaledDifferenceCost capacity 1 b+1+addScaledDifferenceCost cells width d)))+8+a*(5*cells+3) ≤ _
  nlinarith

theorem formulaClauseCount_le (program : Machine.Program) (cells width capacity : Nat) :
    formulaClauseCount program cells width capacity ≤
      generatorCountCoefficient program*(cells+width+capacity+1) := by
  let size := cells+width+capacity+1
  let a := Cellular.alphabet program
  let h := (oneHotTemplate a).length
  let b := (initialBinaryTemplate program).length
  let d := transitionClauseCount program
  have positive : 1≤size := by dsimp [size]; omega
  have hc : cells≤size := by dsimp [size]; omega
  have hw : width≤size := by dsimp [size]; omega
  have hk : capacity≤size := by dsimp [size]; omega
  have first := Nat.mul_le_mul_right h hc
  have second := Nat.mul_le_mul hk (Nat.sub_le a 3)
  have third := Nat.mul_le_mul ((Nat.sub_le width capacity).trans hw) (Nat.sub_le a 1)
  have fourth := Nat.mul_le_mul_right b ((Nat.sub_le capacity 1).trans hk)
  have fifth := Nat.mul_le_mul_right d ((Nat.sub_le cells width).trans hc)
  change cells*h+capacity*(a-3)+(width-capacity)*(a-1)+(capacity-1)*b+(cells-width)*d+1 ≤ 100*(h+a+b+d+1)*size
  nlinarith

def generatorHeaderCoefficient (program : Machine.Program) :=
  20*(generatorCountCoefficient program+1)^2+28*(Cellular.alphabet program+1)^2+1

theorem formulaHeadersBound_le (program : Machine.Program) (cells width capacity : Nat) :
    formulaHeadersBound (cells*Cellular.alphabet program) (formulaClauseCount program cells width capacity) ≤
      generatorHeaderCoefficient program*(cells+width+capacity+1)^2 := by
  let size := cells+width+capacity+1
  have positive : 1≤size := by dsimp [size]; omega
  have count := formulaClauseCount_le program cells width capacity
  change formulaClauseCount program cells width capacity ≤ generatorCountCoefficient program*size at count
  have first : formulaClauseCount program cells width capacity+1≤(generatorCountCoefficient program+1)*size := by nlinarith
  have variablesBound := Nat.mul_le_mul_right (Cellular.alphabet program) (show cells≤size by dsimp [size]; omega)
  have second : cells*Cellular.alphabet program+1≤(Cellular.alphabet program+1)*size := by nlinarith
  have squareFirst := Nat.mul_le_mul_left 20 (Nat.pow_le_pow_left first 2)
  have squareSecond := Nat.mul_le_mul_left 28 (Nat.pow_le_pow_left second 2)
  simp only [mul_pow] at squareFirst squareSecond
  change formulaHeadersBound (cells*Cellular.alphabet program) (formulaClauseCount program cells width capacity) ≤ generatorHeaderCoefficient program*size^2
  unfold formulaHeadersBound generatorHeaderCoefficient
  nlinarith

end Counting.External.CookLevin.StackGenerator
