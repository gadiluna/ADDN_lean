import Counting.ExternalMatchingVariableBlock

namespace Counting.External.MatchingMachine

theorem variableBlockCost_le (a c count : Nat) :
    variableBlockCost a c count ≤ 8000*(a+c+count+1)^3 := by
  let S := a+c+count+1
  have positive : 1 ≤ S := by dsimp [S];omega
  have ac : a ≤ S := by dsimp [S];omega
  have nc : count ≤ S := by dsimp [S];omega
  have first : (2*a+c+3*count+2)^2 ≤ 9*S^2 := by
    calc
      _ ≤ (3*S)^2 := Nat.pow_le_pow_left (by dsimp [S];omega) 2
      _ = _ := by ring
  have last : (2*a+c+2*count+1)^2 ≤ 9*S^2 := by
    calc
      _ ≤ (3*S)^2 := Nat.pow_le_pow_left (by dsimp [S];omega) 2
      _ = _ := by ring
  have product : count*S^2 ≤ S^3 := by
    calc
      _ ≤ S*S^2 := Nat.mul_le_mul_right _ nc
      _ = _ := by ring
  have totalProduct : count*(2*a+c+3*count+2)^2 ≤ 9*S^3 := by
    calc
      _ ≤ count*(9*S^2) := Nat.mul_le_mul_left _ first
      _ = 9*(count*S^2) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ product
  have square : S^2 ≤ S^3 := Nat.pow_le_pow_right positive (by decide)
  have linear : S ≤ S^3 := Nat.le_self_pow (by decide) _
  have constant : 1 ≤ S^3 := Nat.one_le_pow _ _ positive
  have expanded : variableBlockCost a c count =
      410*(count*(2*a+c+3*count+2)^2)+8*count+410*(2*a+c+2*count+1)^2+18*a+24 := by
    unfold variableBlockCost
    ring
  rw [expanded]
  change _ ≤ 8000*S^3
  omega

end Counting.External.MatchingMachine
