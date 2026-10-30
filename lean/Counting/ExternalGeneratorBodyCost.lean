import Counting.ExternalGeneratorBody

namespace Counting.External.CookLevin.StackGenerator
open StackMachine.Routine InitialRows

def formulaBodyCoefficient (program : Machine.Program) :=
  centeredLiteralsCoefficient (Cellular.alphabet program) (finalOffsets program)+
    emitScaledNaturalCoefficient (finalOffsets program).length+transitionCellCoefficient program+
    initialCoefficient program+initialBinaryCoefficient program+oneHotBodyCoefficient (Cellular.alphabet program)+350

/-- Polynomial cost of every concrete clause-emission loop, including
coordinate arithmetic, branching, and cleanup. -/
theorem formulaBodyBound_polynomial (program : Machine.Program) (time : Nat) {width : Nat} (setup : Setup width) :
    formulaBodyBound program time width setup.capacity ≤
      formulaBodyCoefficient program*((time+1)*(width+1)+1)^4 := by
  let size := (time+1)*(width+1)
  have ht : time≤size := by dsimp only [size]; nlinarith
  have hw : width≤size := by dsimp only [size]; nlinarith
  have hn : (time+1)*width≤size := by dsimp only [size]; nlinarith
  have cube : (size+1)^3≤(size+1)^4 := Nat.pow_le_pow_right (by omega) (by omega)
  have widthPower : (width+1)^3≤(size+1)^4 :=
    (Nat.pow_le_pow_left (Nat.add_le_add_right hw 1) 3).trans cube
  have cellsPower : ((time+1)*width+1)^3≤(size+1)^4 :=
    (Nat.pow_le_pow_left (Nat.add_le_add_right hn 1) 3).trans cube
  have finalBound := (finalClauseBound_polynomial program time width).trans
    (Nat.mul_le_mul_left _ cube)
  have transitions := transitionsBound_polynomial program time width
  have initial := (initialRowBound_polynomial program setup).trans (Nat.mul_le_mul_left _ widthPower)
  have hot := (oneHot_time_bound ((time+1)*width) (Cellular.alphabet program)).trans (Nat.mul_le_mul_left _ cellsPower)
  have grow : size+1≤(size+1)^4 := by
    simpa only [pow_one] using Nat.pow_le_pow_right (show 0<size+1 by omega) (show 1≤4 by omega)
  have linear : 5*time+6≤11*(size+1)^4 := by nlinarith
  change formulaBodyBound program time width setup.capacity ≤ formulaBodyCoefficient program*(size+1)^4
  change transitionsBound program time width≤(transitionCellCoefficient program+20)*(size+1)^4 at transitions
  unfold formulaBodyBound formulaBodyCoefficient
  nlinarith

end Counting.External.CookLevin.StackGenerator
