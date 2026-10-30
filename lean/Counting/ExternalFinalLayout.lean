import Counting.ExternalCenteredLiterals
import Counting.ExternalTransitionRow

namespace Counting.External.CookLevin.StackGenerator
open StackMachine StackMachine.Routine Tableau FiniteConstraints

def finalOffsets (program : Machine.Program) : List (Nat × Bool) :=
  ((List.finRange (Cellular.alphabet program)).filter (Cellular.accept program)).map (fun value => (value.val,true))

theorem finalClause_raw (program : Machine.Program) (time width : Nat) :
    (@finalClause time width (Cellular.alphabet program) (Cellular.accept program)).map CNFEncoding.literalRaw=
      (List.finRange width).flatMap (fun place =>
        shiftedLiterals (Cellular.alphabet program*(time*width+place.val)) (finalOffsets program)) := by
  simp only [finalClause,List.map_flatMap]
  apply congrArg (fun f => (List.finRange width).flatMap f)
  funext place
  simp [finalOffsets,shiftedLiterals,List.map_map,CNFEncoding.literalRaw,lit,bitIndex,index,finProdFinEquiv,
    Nat.mul_comm,Nat.add_comm,Function.comp_def]

theorem finalClause_length (program : Machine.Program) (time width : Nat) :
    (@finalClause time width (Cellular.alphabet program) (Cellular.accept program)).length=
      (finalOffsets program).length*width := by
  rw [← List.length_map CNFEncoding.literalRaw,finalClause_raw]
  simp [shiftedLiterals,List.length_flatMap,List.sum_replicate,Nat.mul_comm]

def centeredLiteralsCoefficient (alphabet : Nat) (literals : List (Nat × Bool)) :=
  40+10*alphabet+offsetListCoefficient literals*(alphabet+1)^2

theorem centeredLiteralsBound_polynomial (alphabet : Nat) (literals : List (Nat × Bool))
    (time : Nat) {width : Nat} (place : Fin width) :
    centeredLiteralsBound alphabet literals time width place.val≤
      centeredLiteralsCoefficient alphabet literals*((time+1)*width+1)^2 := by
  let nodes := (time+1)*width
  have widthPositive : 1≤width := place.pos
  have timeWidth := Nat.mul_le_mul_left time widthPositive
  have ht : time≤nodes := by dsimp only [nodes]; nlinarith
  have hw : width≤nodes := by dsimp only [nodes]; nlinarith
  have hp : place.val≤nodes := (Nat.le_of_lt place.isLt).trans hw
  have hc : time*width+place.val≤nodes := by dsimp only [nodes]; have := place.isLt; nlinarith
  have coordinates := centerCost_bound time width place.val nodes ht hw hp
  have inner : alphabet*(time*width+place.val)+1≤(alphabet+1)*(nodes+1) := by nlinarith [Nat.mul_le_mul_left alphabet hc]
  have power := Nat.pow_le_pow_left inner 2
  rw [Nat.mul_pow] at power
  have weighted := Nat.mul_le_mul_left (offsetListCoefficient literals) power
  have linear : time*width+place.val+1≤(nodes+1)^2 := by nlinarith
  have weightedLinear := Nat.mul_le_mul_left (6*alphabet+1) linear
  have one : 1≤(nodes+1)^2 := by nlinarith
  have constant := Nat.mul_le_mul_left (3*alphabet+6) one
  change centerCost time width place.val+alphabet*(5*(time*width+place.val)+3)+
      offsetListCoefficient literals*(alphabet*(time*width+place.val)+1)^2+
      (time*width+place.val)+alphabet*(time*width+place.val)+6≤
      (40+10*alphabet+offsetListCoefficient literals*(alphabet+1)^2)*(nodes+1)^2
  nlinarith

end Counting.External.CookLevin.StackGenerator
