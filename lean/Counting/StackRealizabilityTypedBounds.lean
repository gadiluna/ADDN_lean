import Counting.StackRealizabilityTypedCheck
import Counting.RealizabilityRoundInputBounds

namespace Counting.StackMachine.RealizabilityCheck

def typedCoefficient : Nat := 3000000000000000000000000*5^25+2000000

private theorem typed_round_scale (size : Nat) :
    3000000000000000000000000*(5*size)^25=
      (3000000000000000000000000*5^25)*size^25 := by rw [mul_pow,Nat.mul_assoc]

private theorem typed_depth_scale (size : Nat) : 100000*(2*size)^4=1600000*size^4 := by ring

theorem typedCheckCost_input_bound (vista : Executable.Vista) (values : List Nat) (ell order : Nat)
    (valid : vista.valid=true) :
    typedCheckCost vista values ell order ≤
      Complexity.polynomial typedCoefficient 25
        (Encoding.verifierInput.encode (vista,values,ell,order)).length := by
  let L := (Encoding.verifierInput.encode (vista,values,ell,order)).length
  let B := L+1
  have whole : L=((Encoding.list Encoding.node).encode vista.nodes.toList).length+
      (Encoding.natural.encode vista.bottom).length+
      ((Encoding.list Encoding.natural).encode values).length+
      (Encoding.natural.encode ell).length+(Encoding.natural.encode order).length := by
    simp only [L,Encoding.verifierInput,Encoding.vista,Encoding.transport,Encoding.product,List.length_append]
    omega
  have nodes := Encoding.vista_nodes_le_length vista
  have vistaSmall : (Encoding.vista.encode vista).length ≤ L := by
    simp only [L,Encoding.verifierInput,Encoding.product,List.length_append];omega
  have nodeSmall : vista.nodes.size ≤ L := nodes.trans vistaSmall
  have initialBase : (((Encoding.list Encoding.node).encode vista.nodes.toList).length+
      ((Encoding.list Encoding.natural).encode values).length)+ell.size+order.size+1 ≤ B := by
    simp only [Encoding.natural_length] at whole
    dsimp only [B];omega
  have depthBase : ((Encoding.list Encoding.node).encode vista.nodes.toList).length+vista.nodes.size+1 ≤ 2*B := by
    dsimp only [B];omega
  have bottomBase : ((Encoding.list Encoding.natural).encode values).length+vista.nodes.size+1 ≤ 2*B := by
    dsimp only [B];omega
  have roundsBase := allRoundsSize_input_bound vista values.toArray ell order valid
  change allRoundsSize vista values.toArray order ≤ 5*B at roundsBase
  have initialLimit := Nat.mul_le_mul_left 15000 (Nat.pow_le_pow_left initialBase 5)
  have depthLimit := (Nat.mul_le_mul_left 100000 (Nat.pow_le_pow_left depthBase 4)).trans_eq (typed_depth_scale B)
  have roundLimit := (Nat.mul_le_mul_left 3000000000000000000000000
    (Nat.pow_le_pow_left roundsBase 25)).trans_eq (typed_round_scale B)
  have bottomLimit := Nat.mul_le_mul_left 60 bottomBase
  have positive : 1 ≤ B := by dsimp only [B];omega
  have linear : B ≤ B^25 := Nat.le_self_pow (by decide) _
  have fourth : B^4 ≤ B^25 := Nat.pow_le_pow_right positive (by decide)
  have fifth : B^5 ≤ B^25 := Nat.pow_le_pow_right positive (by decide)
  have one : 1 ≤ B^25 := Nat.one_le_pow _ _ positive
  unfold typedCheckCost
  change _ ≤ (3000000000000000000000000*5^25+2000000)*B^25
  rw [Nat.add_mul]
  omega

end Counting.StackMachine.RealizabilityCheck
