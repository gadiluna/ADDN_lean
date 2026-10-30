import Counting.HardnessNetworkMachineBuild
import Counting.HardnessNetworkMachineSizes

namespace Counting.HardnessNetworkMachine
open StackMachine
set_option maxHeartbeats 1800000

/-- A polynomial majorant for the path-group loop, retaining the actual
width and explicit iteration count as separate parameters. -/
def groupCostUpper (width size : Nat) :=
  5*size+size*(100*(2*width+1)^2+4)+100*(width+1)^2+10

def buildCostUpper (q groups width base coefficientLength leaderLength pathLength starLength wordLength rowLength : Nat) :=
  HardnessNetworkDimensions.cost q groups+
    (30*(width+1)^2+1820*(coefficientLength+1)^3+
      (groups+1)*(100*(coefficientLength+1)*(base+2)+26)+20)+
    (30*(width+1)^2+5*leaderLength+groupCostUpper width (base+1)+
      groups*(groupCostUpper width base+7)+width+30)+
    (130*(width+1)^2+5*leaderLength+5*width+(5*rowLength+4)*width+rowLength+20)+
    (40*(width+1)^2+30*(base+1)^2+5*base+(5*pathLength+4)*base+5*starLength+20)+
    2*wordLength+9

theorem buildNetworkCost_le_upper (q : Nat) (coefficients : List Nat) :
    buildNetworkCost q coefficients ≤
      buildCostUpper q coefficients.tail.length (networkOrder (q+3) coefficients) (q+3)
        ((Encoding.list Encoding.natural).encode coefficients).length
        ((Encoding.list Encoding.natural).encode (leaderRow (q+3) coefficients)).length
        ((Encoding.list (Encoding.list Encoding.natural)).encode (pathMatrix (q+3) coefficients)).length
        ((Encoding.list (Encoding.list Encoding.natural)).encode (starMatrix (q+3) coefficients)).length
        (networkWord (q+3) coefficients).length
        ((Encoding.list Encoding.natural).encode (oneHotRow (networkOrder (q+3) coefficients) 0)).length := by
  unfold buildNetworkCost buildCostUpper leaderRowCost leaderBlockCost pathCost groupCost groupCostUpper
    starCost serializationCost
  simp only [Nat.add_assoc,Nat.reduceAdd]
  gcongr <;> omega

theorem buildCostUpper_mono {q g n b c l p s w h q' g' n' b' c' l' p' s' w' h' : Nat}
    (hq : q ≤ q') (hg : g ≤ g') (hn : n ≤ n') (hb : b ≤ b') (hc : c ≤ c')
    (hl : l ≤ l') (hp : p ≤ p') (hs : s ≤ s') (hw : w ≤ w') (hh : h ≤ h') :
    buildCostUpper q g n b c l p s w h ≤ buildCostUpper q' g' n' b' c' l' p' s' w' h' := by
  unfold buildCostUpper groupCostUpper HardnessNetworkDimensions.cost
  gcongr

theorem buildCostUpper_envelope (S : Nat) (positive : 1 ≤ S) :
    buildCostUpper S S (S^2) S (20*S^3) (12*S^4) (17*S^4) (17*S^4) (25*S^5) (3*S^2+3) ≤
      100000000*S^9 := by
  have p0 : 1 ≤ S^9 := Nat.one_le_pow _ _ positive
  have p1 : S ≤ S^9 := Nat.le_self_pow (by decide) _
  have p2 : S^2 ≤ S^9 := Nat.pow_le_pow_right positive (by decide)
  have p3 : S^3 ≤ S^9 := Nat.pow_le_pow_right positive (by decide)
  have p4 : S^4 ≤ S^9 := Nat.pow_le_pow_right positive (by decide)
  have p5 : S^5 ≤ S^9 := Nat.pow_le_pow_right positive (by decide)
  have p6 : S^6 ≤ S^9 := Nat.pow_le_pow_right positive (by decide)
  have p7 : S^7 ≤ S^9 := Nat.pow_le_pow_right positive (by decide)
  have p8 : S^8 ≤ S^9 := Nat.pow_le_pow_right positive (by decide)
  unfold buildCostUpper groupCostUpper HardnessNetworkDimensions.cost
  ring_nf
  nlinarith only [p0,p1,p2,p3,p4,p5,p6,p7,p8]

/-- The bound depends on the actual explicit source cardinalities, not on
unary expansion of a binary arc multiplicity. Every cached matrix is paid for. -/
theorem buildNetworkCost_polynomial (input : X3CEncoding.Input) (L : Nat)
    (qBound : input.1 ≤ L) (countBound : input.2.1 ≤ L) :
    buildNetworkCost input.1 (External.CoefficientMachine.inputCoefficients input) ≤
      100000000*(L+4)^9 := by
  let S:=L+4
  let values:=External.CoefficientMachine.inputCoefficients input
  have population:=coefficient_networkOrder_bound input L qBound countBound
  have widthBound : networkOrder (input.1+3) values ≤ S^2 := by
    change networkOrder (input.1+3) values+1 ≤ S^2 at population
    omega
  have groupsBound : values.tail.length ≤ S := by
    simp only [values,List.length_tail,External.CoefficientMachine.inputCoefficients_length]
    dsimp only [S]
    omega
  have row:=oneHotRow_encoded_length (networkOrder (input.1+3) values) 0 (by simp [networkOrder])
  have rowBound : ((Encoding.list Encoding.natural).encode (oneHotRow (networkOrder (input.1+3) values) 0)).length ≤
      3*S^2+3 := by omega
  have envelope:=buildCostUpper_mono
    (show input.1 ≤ S by dsimp only [S];omega) groupsBound widthBound
    (show input.1+3 ≤ S by dsimp only [S];omega)
    (External.CoefficientMachine.inputCoefficients_encoding_length input L qBound countBound)
    (coefficient_leaderRow_encoded_bound input L qBound countBound)
    (coefficient_pathMatrix_encoded_bound input L qBound countBound)
    (coefficient_starMatrix_encoded_bound input L qBound countBound)
    (coefficient_networkWord_encoded_bound input L qBound countBound) rowBound
  exact (buildNetworkCost_le_upper input.1 values).trans
    (envelope.trans (buildCostUpper_envelope S (by dsimp only [S];omega)))

theorem buildNetworkCost_polynomial_shifted (input : X3CEncoding.Input) (L : Nat)
    (qBound : input.1 ≤ L) (countBound : input.2.1 ≤ L) :
    buildNetworkCost input.1 (External.CoefficientMachine.inputCoefficients input) ≤
      (100000000*4^9)*(L+1)^9 := by
  apply (buildNetworkCost_polynomial input L qBound countBound).trans
  have shifted : L+4 ≤ 4*(L+1) := by omega
  calc
    _ ≤ 100000000*(4*(L+1))^9 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left shifted _)
    _ = _ := by ring

end Counting.HardnessNetworkMachine
