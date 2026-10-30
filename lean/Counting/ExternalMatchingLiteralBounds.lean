import Counting.ExternalMatchingLiteralLayout

namespace Counting.External.MatchingMachine

theorem generateLiteralCost_mono {a b c d e f A B C D E F : Nat}
    (ha : a ≤ A) (hb : b ≤ B) (hc : c ≤ C) (hd : d ≤ D) (he : e ≤ E) (hf : f ≤ F) :
    generateLiteralCost a b c d e f ≤ generateLiteralCost A B C D E F := by
  unfold generateLiteralCost
  gcongr

theorem generateLiteralCost_polynomial (input n width occurrence shift first bound : Nat)
    (hInput : input ≤ bound) (hn : n ≤ bound) (hw : width ≤ bound)
    (ho : occurrence ≤ bound) (hs : shift ≤ bound) (hf : first ≤ bound) :
    generateLiteralCost input n width occurrence shift first ≤ 8000*(bound+1)^4 := by
  let S := bound+1
  have positive : 1 ≤ S := by dsimp [S];omega
  have inputBound : (input+n+1)^3 ≤ 8*S^4 := by
    calc
      _ ≤ (2*S)^3 := Nat.pow_le_pow_left (by dsimp [S];omega) 3
      _ = 8*S^3 := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right positive (by decide))
  have portBound : (n+width+occurrence+shift+1)^2 ≤ 16*S^4 := by
    calc
      _ ≤ (4*S)^2 := Nat.pow_le_pow_left (by dsimp [S];omega) 2
      _ = 16*S^2 := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right positive (by decide))
  have product : n*width ≤ bound^2 := by simpa only [pow_two] using Nat.mul_le_mul hn hw
  have edgeBase : 2*first+n*width+occurrence+shift+1 ≤ 4*S^2 := by dsimp [S];nlinarith only [product,hf,ho,hs]
  have edgeBound : (2*first+n*width+occurrence+shift+1)^2 ≤ 16*S^4 := by
    calc
      _ ≤ (4*S^2)^2 := Nat.pow_le_pow_left edgeBase 2
      _ = _ := by ring
  have clearBase : n+first+n*width+occurrence+shift+2 ≤ 4*S^2 := by dsimp [S];nlinarith only [product,hn,hf,ho,hs]
  have square : S^2 ≤ S^4 := Nat.pow_le_pow_right positive (by decide)
  have linear : S ≤ S^4 := Nat.le_self_pow (by decide) _
  have constant : 1 ≤ S^4 := Nat.one_le_pow _ _ positive
  have firstS : first ≤ S := by dsimp [S];omega
  change _ ≤ 8000*S^4
  unfold generateLiteralCost
  omega

end Counting.External.MatchingMachine
