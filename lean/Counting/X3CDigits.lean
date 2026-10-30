import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Tactic

namespace Counting.X3C

def digitValue (base : ℕ) {n : ℕ} (digit : Fin n → ℕ) : ℕ :=
  ∑ i : Fin n, digit i * base ^ i.val

theorem digitValue_succ (base n : ℕ) (digit : Fin (n + 1) → ℕ) :
    digitValue base digit = digit 0 + base * digitValue base (fun i => digit i.succ) := by
  unfold digitValue
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, Nat.mul_one, Fin.val_succ, pow_succ]
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem digitValue_lt_pow (base : ℕ) (_positive : 1 < base) {n : ℕ}
    (digit : Fin n → ℕ) (bounded : ∀ i, digit i < base) : digitValue base digit < base ^ n := by
  induction n with
  | zero => simp [digitValue]
  | succ n ih =>
    rw [digitValue_succ, pow_succ]
    have tail := ih (fun i => digit i.succ) (fun i => bounded i.succ)
    have head := bounded 0
    nlinarith

theorem digitValue_injective (base : ℕ) (positive : 1 < base) {n : ℕ}
    (a b : Fin n → ℕ) (ha : ∀ i, a i < base) (hb : ∀ i, b i < base)
    (same : digitValue base a = digitValue base b) : a = b := by
  induction n with
  | zero => exact funext (fun i => Fin.elim0 i)
  | succ n ih =>
    rw [digitValue_succ, digitValue_succ] at same
    have head := congrArg (· % base) same
    simp only [Nat.add_mod, Nat.mul_mod_right, Nat.add_zero,
      Nat.mod_eq_of_lt (ha 0), Nat.mod_eq_of_lt (hb 0)] at head
    have tail : digitValue base (fun i => a i.succ) = digitValue base (fun i => b i.succ) := by
      nlinarith
    have tails := ih (fun i => a i.succ) (fun i => b i.succ)
      (fun i => ha i.succ) (fun i => hb i.succ) tail
    funext i
    refine Fin.cases head (fun j => congrFun tails j) i

theorem high_digit_unique (base n : ℕ) (positive : 1 < base)
    (a b : Fin n → ℕ) (ha : ∀ i, a i < base) (hb : ∀ i, b i < base)
    (k q : ℕ) (same : k * base ^ n + digitValue base a = q * base ^ n + digitValue base b) :
    k = q ∧ a = b := by
  have aSmall := digitValue_lt_pow base positive a ha
  have bSmall := digitValue_lt_pow base positive b hb
  have powerPositive : 0 < base ^ n := pow_pos (by omega) _
  have high : k = q := by
    by_contra different
    rcases lt_or_gt_of_ne different with lower | higher
    · have : k + 1 ≤ q := lower
      nlinarith
    · have : q + 1 ≤ k := higher
      nlinarith
  refine ⟨high, digitValue_injective base positive a b ha hb ?_⟩
  rw [high] at same
  exact Nat.add_left_cancel same

theorem set_digitValue (base n : ℕ) (S : Finset (Fin n)) :
    digitValue base (fun e => if e ∈ S then 1 else 0) = ∑ e ∈ S, base ^ e.val := by
  classical
  simp only [digitValue, ite_mul, Nat.one_mul, Nat.zero_mul]
  rw [← Finset.sum_filter]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]

theorem set_value_injective (base n : ℕ) (positive : 1 < base)
    (S T : Finset (Fin n)) (same : (∑ e ∈ S, base ^ e.val) = ∑ e ∈ T, base ^ e.val) : S = T := by
  classical
  have digits := digitValue_injective base positive
    (fun e => if e ∈ S then 1 else 0) (fun e => if e ∈ T then 1 else 0)
    (fun e => by split <;> omega) (fun e => by split <;> omega)
    (by simpa only [set_digitValue] using same)
  ext e
  have equal := congrFun digits e
  by_cases hs : e ∈ S <;> by_cases ht : e ∈ T <;> simp_all

end Counting.X3C
