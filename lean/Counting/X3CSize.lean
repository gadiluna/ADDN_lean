import Counting.X3CEquation
import Mathlib.Data.Nat.Size

namespace Counting.X3C

theorem target_lt_base_power (q : ℕ) : target q < base q ^ (3 * q + 1) := by
  have h := target_lt q
  have bound : q + 1 ≤ base q := by unfold base; omega
  have scaled := Nat.mul_le_mul_right (high q) bound
  rw [pow_succ]
  unfold high at scaled
  exact h.trans_le (by simpa only [high, Nat.mul_comm] using scaled)

theorem Instance.coefficient_le_target {q m : ℕ} (I : Instance q m) (large : 2 ≤ q)
    (i : Option (Fin m)) : I.coefficient i ≤ target q := by
  cases i with
  | none => exact le_rfl
  | some j => exact (I.triple_coefficient_lt_target large j).le

theorem Instance.coefficient_lt_base_power {q m : ℕ} (I : Instance q m) (large : 2 ≤ q)
    (i : Option (Fin m)) : I.coefficient i < base q ^ (3 * q + 1) :=
  (I.coefficient_le_target large i).trans_lt (target_lt_base_power q)

/-- Natural-number binary width of a quantity bounded by a power. -/
theorem size_le_power_width (a b n : ℕ) (bounded : a < b ^ n) :
    Nat.size a ≤ n * Nat.size b := by
  apply Nat.size_le.mpr
  have baseBound : b ≤ 2 ^ Nat.size b := (Nat.size_le.mp (le_refl (Nat.size b))).le
  have powerBound := Nat.pow_le_pow_left baseBound n
  rw [← pow_mul] at powerBound
  simpa only [Nat.mul_comm] using bounded.trans_le powerBound

/-- The q*log(q+3) coefficient-width estimate, with an explicit constant. -/
theorem Instance.coefficient_size {q m : ℕ} (I : Instance q m) (large : 2 ≤ q)
    (i : Option (Fin m)) : Nat.size (I.coefficient i) ≤ (3 * q + 1) * Nat.size (q + 3) :=
  size_le_power_width _ _ _ (I.coefficient_lt_base_power large i)

def baselineMass (q m : ℕ) : ℕ := 1 + (m + 1) * base q

def Instance.weightedTarget {q m : ℕ} (I : Instance q m) : ℕ :=
  base q * (∑ i : Option (Fin m), I.coefficient i) + target q

theorem Instance.weightedTarget_lt {q m : ℕ} (I : Instance q m) (large : 2 ≤ q) :
    I.weightedTarget < baselineMass q m * base q ^ (3 * q + 1) := by
  have sumBound : (∑ i : Option (Fin m), I.coefficient i) ≤
      (m + 1) * base q ^ (3 * q + 1) := by
    calc
      _ ≤ ∑ _i : Option (Fin m), base q ^ (3 * q + 1) :=
        Finset.sum_le_sum (fun i _ => (I.coefficient_lt_base_power large i).le)
      _ = _ := by simp
  have scaled := Nat.mul_le_mul_left (base q) sumBound
  have targetBound := target_lt_base_power q
  unfold Instance.weightedTarget baselineMass
  nlinarith

theorem Instance.weightedTarget_size {q m : ℕ} (I : Instance q m) (large : 2 ≤ q) :
    Nat.size I.weightedTarget ≤ Nat.size (baselineMass q m) + (3 * q + 1) * Nat.size (base q) := by
  apply Nat.size_le.mpr
  have rBound : baselineMass q m ≤ 2 ^ Nat.size (baselineMass q m) :=
    (Nat.size_le.mp (le_refl (Nat.size (baselineMass q m)))).le
  have bBound : base q ≤ 2 ^ Nat.size (base q) := (Nat.size_le.mp (le_refl (Nat.size (base q)))).le
  have powerBound := Nat.pow_le_pow_left bBound (3 * q + 1)
  have productBound := Nat.mul_le_mul rBound powerBound
  rw [← pow_mul, ← pow_add] at productBound
  have h := (I.weightedTarget_lt large).trans_le productBound
  simpa only [Nat.mul_comm] using h

end Counting.X3C
