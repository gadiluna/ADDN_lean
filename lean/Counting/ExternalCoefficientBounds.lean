import Counting.ExternalCoefficientGenerator
import Counting.ExternalCoefficientSizes

namespace Counting.External.CoefficientMachine
open StackMachine
set_option maxHeartbeats 1800000

def costFromLengths (input q count baseLength highLength targetLength width output : Nat) :=
  4000*(input+3*q+1)^3+1+(6*count+4+1+
    (100*(count+2)^2+1+((100*(q+1)^2+1+
      (highCost baseLength (3*q)+1+baselineCost q (3*q) baseLength highLength width))+1+
      (9*targetLength+8+1+(count*(rowCost input (3*q) baseLength highLength width+2)+1))+1+
      (2*output+4))))

theorem generatorCost_lengths (input q count output : Nat) :
    generatorCost input q count output=costFromLengths input q count
      (X3C.base q).bits.length (X3C.high q).bits.length (X3C.target q).bits.length
      ((3*q+1)*(X3C.base q).size) output := rfl

theorem costFromLengths_mono {i q c b h t w o i' q' c' b' h' t' w' o' : Nat}
    (hi : i ≤ i') (hq : q ≤ q') (hc : c ≤ c') (hb : b ≤ b') (hh : h ≤ h')
    (ht : t ≤ t') (hw : w ≤ w') (ho : o ≤ o') :
    costFromLengths i q c b h t w o ≤ costFromLengths i' q' c' b' h' t' w' o' := by
  unfold costFromLengths highCost baselineCost geometricStepCost rowCost tripleCost atomCost
    NaturalPower.accumulatePowerCost NaturalPower.iterationCost
  gcongr

theorem costFromLengths_envelope (S : Nat) (positive : 1 ≤ S) :
    costFromLengths S S S S (4*S^2) (4*S^2) (4*S^2) (20*S^3) ≤ 1000000000000*S^8 := by
  have p0 : 1 ≤ S^8 := Nat.one_le_pow _ _ positive
  have p1 : S ≤ S^8 := Nat.le_self_pow (by decide) _
  have p2 : S^2 ≤ S^8 := Nat.pow_le_pow_right positive (by decide)
  have p3 : S^3 ≤ S^8 := Nat.pow_le_pow_right positive (by decide)
  have p4 : S^4 ≤ S^8 := Nat.pow_le_pow_right positive (by decide)
  have p5 : S^5 ≤ S^8 := Nat.pow_le_pow_right positive (by decide)
  have p6 : S^6 ≤ S^8 := Nat.pow_le_pow_right positive (by decide)
  have p7 : S^7 ≤ S^8 := Nat.pow_le_pow_right positive (by decide)
  unfold costFromLengths highCost baselineCost geometricStepCost rowCost tripleCost atomCost
    NaturalPower.accumulatePowerCost NaturalPower.iterationCost
  ring_nf
  nlinarith only [p0,p1,p2,p3,p4,p5,p6,p7]

theorem generatorCost_polynomial (input : X3CEncoding.Input)
    (L : Nat) (qBound : input.1 ≤ L) (countBound : input.2.1 ≤ L) :
    generatorCost L input.1 input.2.1
      ((Encoding.list Encoding.natural).encode (inputCoefficients input)).length ≤
      65536000000000000*(L+1)^8 := by
  let S:=L+4
  have baseBound : (X3C.base input.1).bits.length ≤ S := by
    rw [Encoding.bits_length]
    have bound : (X3C.base input.1).size ≤ input.1+3 := Nat.size_le.mpr Nat.lt_two_pow_self
    dsimp only [S];omega
  have widthBound : (3*input.1+1)*(X3C.base input.1).size ≤ 4*S^2 := coefficient_width_bound _ _ qBound
  have highBound : (X3C.high input.1).bits.length ≤ 4*S^2 := by
    have power:=NaturalPower.power_bits_length (X3C.base input.1).bits (3*input.1)
    rw [Encoding.value_bits] at power
    change (X3C.high input.1).bits.length ≤ 3*input.1*(X3C.base input.1).bits.length+1 at power
    have product : 3*input.1*(X3C.base input.1).bits.length ≤ 3*S*S := by
      apply Nat.mul_le_mul
      · dsimp only [S];omega
      · exact baseBound
    have pos : 1 ≤ S := by dsimp only [S];omega
    nlinarith only [power,product,pos]
  have targetBound : (X3C.target input.1).bits.length ≤ 4*S^2 := by
    rw [Encoding.bits_length]
    exact (X3C.size_le_power_width _ _ _ (X3C.target_lt_base_power input.1)).trans widthBound
  have outputBound := inputCoefficients_encoding_length input L qBound countBound
  rw [generatorCost_lengths]
  have envelope := costFromLengths_mono (i:=L) (q:=input.1) (c:=input.2.1)
    (by dsimp only [S];omega : L ≤ S) (by dsimp only [S];omega : input.1 ≤ S)
    (by dsimp only [S];omega : input.2.1 ≤ S) baseBound highBound targetBound widthBound outputBound
  apply envelope.trans
  apply (costFromLengths_envelope S (by dsimp only [S];omega)).trans
  have shifted : S ≤ 4*(L+1) := by dsimp only [S];omega
  calc
    1000000000000*S^8 ≤ 1000000000000*(4*(L+1))^8 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left shifted _)
    _ = _ := by ring

end Counting.External.CoefficientMachine
