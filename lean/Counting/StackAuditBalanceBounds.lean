import Counting.StackAuditBalanceRounds
import Counting.StackAuditBalanceInputRead
import Counting.EncodingVerifier

namespace Counting.StackMachine.AuditBalance
set_option maxHeartbeats 1600000

def balanceScale (vista : Executable.Vista) (weights : Array Nat) : Nat :=
  (Encoding.vista.encode vista).length+((Encoding.array Encoding.natural).encode weights).length+
    vista.nodes.size+2

def roundCoefficient : Nat := 2000000000000000

theorem roundBudget_uniform (vista : Executable.Vista) (weights : Array Nat) (round : Nat)
    (inside : round ≤ vista.nodes.size) :
    roundBudget vista weights round ≤ roundCoefficient*(balanceScale vista weights)^16 := by
  let S:=balanceScale vista weights
  have positive : 1 ≤ S := by dsimp only [S,balanceScale];omega
  have nodes : vista.nodes.size ≤ S := by dsimp only [S,balanceScale];omega
  have first : round.size ≤ round := Nat.size_le.mpr Nat.lt_two_pow_self
  have second : (round+1).size ≤ round+1 := Nat.size_le.mpr Nat.lt_two_pow_self
  have base : (Encoding.vista.encode vista).length+((Encoding.array Encoding.natural).encode weights).length+
      round.size+(round+1).size+vista.nodes.size+2 ≤ 3*S := by
    dsimp only [S,balanceScale]
    omega
  have power:=Nat.mul_le_mul_left 100020100 (Nat.pow_le_pow_left base 15)
  have scaled : 100020100*((Encoding.vista.encode vista).length+
      ((Encoding.array Encoding.natural).encode weights).length+round.size+(round+1).size+vista.nodes.size+2)^15
      ≤ 1435179113030700*S^15 := by
    calc
      _ ≤ 100020100*(3*S)^15 := power
      _ = _ := by ring
  have multiplied := Nat.mul_le_mul nodes (Nat.add_le_add_right scaled 2)
  have level : levelBudget vista weights round vista.nodes.size ≤
      1435179113030700*S^16+2*S+1 := by
    calc
      _ ≤ S*(1435179113030700*S^15+2)+1 := Nat.add_le_add_right multiplied 1
      _ = _ := by ring
  have linear : S ≤ S^16 := Nat.le_self_pow (by decide) _
  have one : 1 ≤ S^16 := Nat.one_le_pow _ _ positive
  change roundBudget vista weights round ≤ roundCoefficient*S^16
  dsimp only [roundBudget,roundCoefficient]
  omega

theorem roundsBudget_uniform (vista : Executable.Vista) (weights : Array Nat) (start count : Nat)
    (inside : start+count ≤ vista.nodes.size) :
    roundsBudget vista weights start count ≤
      count*(roundCoefficient*(balanceScale vista weights)^16+2)+1 := by
  induction count generalizing start with
  | zero => simp [roundsBudget]
  | succ count ih =>
    have body:=roundBudget_uniform vista weights start (by omega)
    have rest:=ih (start+1) (by omega)
    rw [roundsBudget]
    simp only [Nat.add_mul,Nat.one_mul]
    omega

theorem roundsBudget_polynomial (anchor : Nat) (vista : Executable.Vista) (weights : Array Nat)
    (fits : anchor ≤ vista.nodes.size) :
    roundsBudget vista weights 0 (anchor-1) ≤
      10000000000000000000000000*((balanceInputWord anchor vista weights).length+1)^17 := by
  let L:=(balanceInputWord anchor vista weights).length+1
  let S:=balanceScale vista weights
  have positive : 1 ≤ L := by dsimp only [L];omega
  have inputSize : (balanceInputWord anchor vista weights).length=
      2*anchor.size+1+(2*(Encoding.vista.encode vista).length+1)+
        ((Encoding.array Encoding.natural).encode weights).length := by
    simp only [balanceInputWord,AuditPropagation.propagationInputWord,
      AuditPropagation.propagationInputCodec,Encoding.product,Encoding.framed,
      List.length_append,Encoding.natural_length,Encoding.frame_length]
    omega
  have nodes:=Encoding.vista_nodes_le_length vista
  have count : anchor-1 ≤ L := by dsimp only [L];omega
  have scale : S ≤ 3*L := by dsimp only [S,balanceScale,L];omega
  have budget:=roundsBudget_uniform vista weights 0 (anchor-1) (by omega)
  have body:=Nat.mul_le_mul_left roundCoefficient (Nat.pow_le_pow_left scale 16)
  have product:=Nat.mul_le_mul count (Nat.add_le_add_right body 2)
  have combined : roundsBudget vista weights 0 (anchor-1) ≤
      86093442000000000000000*L^17+2*L+1 := by
    calc
      _ ≤ (anchor-1)*(roundCoefficient*S^16+2)+1 := budget
      _ ≤ L*(roundCoefficient*(3*L)^16+2)+1 := Nat.add_le_add_right product 1
      _ = _ := by norm_num only [roundCoefficient];ring
  have linear : L ≤ L^17 := Nat.le_self_pow (by decide) _
  have one : 1 ≤ L^17 := Nat.one_le_pow _ _ positive
  change _ ≤ 10000000000000000000000000*L^17
  omega

end Counting.StackMachine.AuditBalance
