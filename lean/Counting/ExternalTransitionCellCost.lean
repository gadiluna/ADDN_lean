import Counting.ExternalTransitionCell

namespace Counting.External.CookLevin.StackGenerator

def transitionCellCoefficient (program : Machine.Program) :=
  200+50*Cellular.alphabet program+transitionCoefficient program*(Cellular.alphabet program+1)^2

/-- Cost covers coordinate construction, scaling, encoded clauses and the
restoration of every temporary base. It is measured in stack transitions. -/
theorem transitionCellBound_polynomial (program : Machine.Program) {time width : Nat}
    (round : Fin time) (place : Fin width) :
    transitionCellBound program time width round.val place.val≤
      transitionCellCoefficient program*((time+1)*width+1)^2 := by
  let nodes := (time+1)*width
  let alphabet := Cellular.alphabet program
  let coefficient := transitionCoefficient program
  have widthPositive : 1≤width := place.pos
  have timeWidth := Nat.mul_le_mul_left time widthPositive
  have roundBound : round.val≤nodes := by dsimp only [nodes]; have := round.isLt; nlinarith
  have widthBound : width≤nodes := by dsimp only [nodes]; nlinarith
  have placeBound : place.val≤nodes := Nat.le_trans (Nat.le_of_lt place.isLt) widthBound
  have coordinatesBound := coordinatesCost_bound round.val width place.val nodes roundBound widthBound placeBound
  have nodeSquare : nodes≤(nodes+1)^2 := by nlinarith
  have oneSquare : 1≤(nodes+1)^2 := by nlinarith
  have scaledLinear := Nat.mul_le_mul_left (7*alphabet+1) nodeSquare
  have scaledConstant := Nat.mul_le_mul_left (3*alphabet+5) oneSquare
  have cleanLinear := Nat.mul_le_mul_left alphabet nodeSquare
  have cleanConstant := Nat.mul_le_mul_left 5 oneSquare
  have finalConstant := Nat.mul_le_mul_left 3 oneSquare
  have inner : alphabet*nodes+1≤(alphabet+1)*(nodes+1) := by nlinarith
  have power := Nat.pow_le_pow_left inner 2
  rw [Nat.mul_pow] at power
  have emitted := Nat.mul_le_mul_left coefficient power
  change coordinatesCost round.val width place.val+
      4*((7*alphabet+1)*nodes+3*alphabet+5)+coefficient*(alphabet*nodes+1)^2+4*(alphabet*nodes+5)+3≤
      (200+50*alphabet+coefficient*(alphabet+1)^2)*(nodes+1)^2
  nlinarith

end Counting.External.CookLevin.StackGenerator
