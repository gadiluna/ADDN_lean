import Counting.X3CDigits

namespace Counting.X3C

/-- The universe is explicitly Fin(3*q); no binary-coded implicit universe
is used. Triples are indexed, have three distinct elements, and do not
duplicate each other. -/
structure Instance (q m : ℕ) where
  triples : Fin m → Finset (Fin (3 * q))
  triple_card : ∀ j, (triples j).card = 3
  distinct : Function.Injective triples

def base (q : ℕ) : ℕ := q + 3
def high (q : ℕ) : ℕ := base q ^ (3 * q)
def ones (q : ℕ) : ℕ := digitValue (base q) (fun _ : Fin (3 * q) => 1)
def target (q : ℕ) : ℕ := q * high q + ones q

def Instance.tripleValue {q m : ℕ} (I : Instance q m) (j : Fin m) : ℕ :=
  ∑ e ∈ I.triples j, base q ^ e.val

def Instance.coefficient {q m : ℕ} (I : Instance q m) : Option (Fin m) → ℕ
  | none => target q
  | some j => high q + I.tripleValue j

def Instance.IsExactCover {q m : ℕ} (I : Instance q m) (chosen : Finset (Fin m)) : Prop :=
  ∀ e : Fin (3 * q), (chosen.filter (fun j => e ∈ I.triples j)).card = 1

@[simp] theorem base_gt_one (q : ℕ) : 1 < base q := by unfold base; omega
theorem high_positive (q : ℕ) : 0 < high q := pow_pos (by unfold base; omega) _

theorem ones_lt_high (q : ℕ) : ones q < high q :=
  digitValue_lt_pow (base q) (base_gt_one q) _ (fun _ => base_gt_one q)

theorem ones_positive (q : ℕ) (positive : 0 < q) : 0 < ones q := by
  let e : Fin (3 * q) := ⟨0, by omega⟩
  have term : 1 ≤ ones q := by
    simpa only [ones, digitValue, e, pow_zero, Nat.mul_one] using
      Finset.single_le_sum (f := fun e : Fin (3 * q) => 1 * base q ^ e.val)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ e)
  omega

theorem target_lt (q : ℕ) : target q < (q + 1) * high q := by
  have := ones_lt_high q
  unfold target
  nlinarith

theorem target_positive (q : ℕ) (positive : 0 < q) : 0 < target q := by
  have := ones_positive q positive
  unfold target
  omega

theorem target_gt_high (q : ℕ) (large : 2 ≤ q) : high q < target q := by
  have := high_positive q
  have := ones_positive q (by omega)
  unfold target
  nlinarith

theorem Instance.tripleValue_lt_high {q m : ℕ} (I : Instance q m) (j : Fin m) :
    I.tripleValue j < high q := by
  rw [Instance.tripleValue, ← set_digitValue]
  apply digitValue_lt_pow _ (base_gt_one q)
  intro e
  split <;> have := base_gt_one q <;> omega

theorem Instance.tripleValue_positive {q m : ℕ} (I : Instance q m) (j : Fin m) :
    0 < I.tripleValue j := by
  have nonempty : (I.triples j).Nonempty := Finset.card_pos.mp (by rw [I.triple_card]; decide)
  obtain ⟨e, he⟩ := nonempty
  exact lt_of_lt_of_le (pow_pos (by unfold base; omega) _)
    (Finset.single_le_sum (f := fun e => base q ^ e.val) (fun _ _ => Nat.zero_le _) he)

theorem Instance.coefficient_gt_high {q m : ℕ} (I : Instance q m) (large : 2 ≤ q)
    (j : Option (Fin m)) : high q < I.coefficient j := by
  cases j with
  | none => exact target_gt_high q large
  | some j =>
      have := I.tripleValue_positive j
      change high q < high q + I.tripleValue j
      omega

theorem Instance.coefficient_positive {q m : ℕ} (I : Instance q m) (large : 2 ≤ q)
    (j : Option (Fin m)) : 0 < I.coefficient j :=
  (high_positive q).trans (I.coefficient_gt_high large j)

theorem Instance.triple_coefficient_lt {q m : ℕ} (I : Instance q m) (j : Fin m) :
    I.coefficient (some j) < 2 * high q := by
  have := I.tripleValue_lt_high j
  change high q + I.tripleValue j < 2 * high q
  omega

theorem Instance.triple_coefficient_lt_target {q m : ℕ} (I : Instance q m)
    (large : 2 ≤ q) (j : Fin m) : I.coefficient (some j) < target q := by
  have first := I.triple_coefficient_lt j
  have positive := high_positive q
  have ones := ones_positive q (by omega)
  unfold target
  nlinarith

theorem Instance.coefficient_injective {q m : ℕ} (I : Instance q m) (large : 2 ≤ q) :
    Function.Injective I.coefficient := by
  intro x y same
  cases x with
  | none =>
    cases y with
    | none => rfl
    | some j => have := I.triple_coefficient_lt_target large j; change target q = _ at same; omega
  | some i =>
    cases y with
    | none => have := I.triple_coefficient_lt_target large i; change _ = target q at same; omega
    | some j =>
      apply congrArg some
      apply I.distinct
      apply set_value_injective (base q) (3 * q) (base_gt_one q)
      exact Nat.add_left_cancel same

end Counting.X3C
