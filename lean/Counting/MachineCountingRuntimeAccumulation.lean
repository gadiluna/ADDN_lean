import Counting.MachineCountingRuntimeInput

namespace Counting.Machine.CountingRuntime
open scoped BigOperators
set_option maxHeartbeats 1800000

/-- Sum the actual charged local step counts over at most the counting
horizon; this is arithmetic and does not postulate a machine implementation. -/
theorem sum_round_costs (cost : Nat → Nat) (coefficient degree population bits rounds : Nat)
    (horizon : rounds ≤ 2*population)
    (each : ∀ round,round < rounds → cost round ≤ coefficient*(population+bits+1)^degree) :
    (∑ round∈Finset.range rounds,cost round) ≤
      2*coefficient*(population+bits+1)^(degree+1) := by
  let N := population+bits+1
  have total := Finset.sum_le_sum (s:=Finset.range rounds)
    (f:=cost) (g:=fun _=>coefficient*N^degree)
    (fun r member=>each r (Finset.mem_range.mp member))
  simp only [Finset.sum_const,Finset.card_range,smul_eq_mul] at total
  have count : rounds ≤ 2*N := by dsimp [N];omega
  have scaled := Nat.mul_le_mul_right (coefficient*N^degree) count
  calc
    _ ≤ rounds*(coefficient*N^degree) := total
    _ ≤ (2*N)*(coefficient*N^degree) := scaled
    _ = 2*coefficient*N^(degree+1) := by rw [pow_succ];ring

/-- Also allow one initialization charge in addition to all live rounds. -/
theorem sum_round_costs_with_initialization (cost : Nat → Nat) (coefficient degree population bits rounds : Nat)
    (horizon : rounds ≤ 2*population+1)
    (each : ∀ round,round < rounds → cost round ≤ coefficient*(population+bits+1)^degree) :
    (∑ round∈Finset.range rounds,cost round) ≤
      3*coefficient*(population+bits+1)^(degree+1) := by
  let N := population+bits+1
  have total := Finset.sum_le_sum (s:=Finset.range rounds)
    (f:=cost) (g:=fun _=>coefficient*N^degree)
    (fun r member=>each r (Finset.mem_range.mp member))
  simp only [Finset.sum_const,Finset.card_range,smul_eq_mul] at total
  have count : rounds ≤ 3*N := by dsimp [N];omega
  have scaled := Nat.mul_le_mul_right (coefficient*N^degree) count
  calc
    _ ≤ rounds*(coefficient*N^degree) := total
    _ ≤ (3*N)*(coefficient*N^degree) := scaled
    _ = 3*coefficient*N^(degree+1) := by rw [pow_succ];ring

/-- The paper's exponential arc assumption gives polynomial binary input
length. Constants and exponents are fixed before choosing the population. -/
theorem arc_power_substitution (population coefficient exponent degree : Nat) :
    (population+(2^(coefficient*population^exponent)).size+1)^degree ≤
      (coefficient+3)^degree*(population+1)^((exponent+1)*degree) := by
  have positive : 1 ≤ population+1 := by omega
  have linear : population+1 ≤ (population+1)^(exponent+1) := Nat.le_self_pow (by omega) _
  have one : 1 ≤ (population+1)^(exponent+1) := Nat.one_le_pow' _ _
  have power : population^exponent ≤ (population+1)^(exponent+1) :=
    (Nat.pow_le_pow_left (Nat.le_succ population) exponent).trans
      (Nat.pow_le_pow_right positive (by omega))
  have base : population+(2^(coefficient*population^exponent)).size+1 ≤
      (coefficient+3)*(population+1)^(exponent+1) := by
    rw [Nat.size_pow,Nat.add_mul]
    have scaled := Nat.mul_le_mul_left coefficient power
    omega
  have result := Nat.pow_le_pow_left base degree
  simpa only [Nat.mul_pow,←Nat.pow_mul] using result

theorem polynomial_arc_round_costs (cost : Nat → Nat) (coefficient degree population arcCoefficient arcExponent rounds : Nat)
    (horizon : rounds ≤ 2*population)
    (each : ∀ round,round < rounds → cost round ≤
      coefficient*(population+(2^(arcCoefficient*population^arcExponent)).size+1)^degree) :
    (∑ round∈Finset.range rounds,cost round) ≤
      (2*coefficient*(arcCoefficient+3)^(degree+1))*(population+1)^((arcExponent+1)*(degree+1)) := by
  have total := sum_round_costs cost coefficient degree population
    (2^(arcCoefficient*population^arcExponent)).size rounds horizon each
  have substituted := Nat.mul_le_mul_left (2*coefficient)
    (arc_power_substitution population arcCoefficient arcExponent (degree+1))
  exact total.trans (substituted.trans_eq (Nat.mul_assoc _ _ _).symm)

/-- Substitute the established codec bound into any already proved fixed
polynomial step bound. The result is in population and binary label size. -/
theorem input_polynomial_substitution (length coefficient degree population bits : Nat)
    (inputBound : length+1 ≤ 4000*(population+bits+1)^6) :
    coefficient*(length+1)^degree ≤
      (coefficient*4000^degree)*(population+bits+1)^(6*degree) := by
  have result := Nat.mul_le_mul_left coefficient (Nat.pow_le_pow_left inputBound degree)
  simpa only [Nat.mul_pow,←Nat.pow_mul,Nat.mul_assoc] using result

end Counting.Machine.CountingRuntime
