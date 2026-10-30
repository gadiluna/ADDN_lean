import Counting.X3CSize

namespace Counting.X3C

variable {q m : ℕ} (I : Instance q m)

def baselineGroups (q m : ℕ) : Option (Fin m) → ℕ
  | none => base q + 1
  | some _ => base q

def coverGroups (q m : ℕ) (chosen : Finset (Fin m)) : Option (Fin m) → ℕ
  | none => base q
  | some j => base q + if j ∈ chosen then 1 else 0

def groupOrder (a : Option (Fin m) → ℕ) : ℕ := 1 + ∑ i, a i

theorem Instance.shifted_sum (a : Option (Fin m) → ℕ) (lower : ∀ i, base q ≤ a i) :
    (∑ i, I.coefficient i * a i) =
      base q * (∑ i, I.coefficient i) + ∑ i, I.coefficient i * (a i - base q) := by
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hi := Nat.add_sub_of_le (lower i)
  nlinarith

theorem Instance.shifted_equation_iff (a : Option (Fin m) → ℕ) (lower : ∀ i, base q ≤ a i) :
    (∑ i, I.coefficient i * a i) = I.weightedTarget ↔
      (∑ i, I.coefficient i * (a i - base q)) = target q := by
  rw [I.shifted_sum a lower]
  exact Nat.add_left_cancel_iff

theorem groupOrder_shifted (a : Option (Fin m) → ℕ) (lower : ∀ i, base q ≤ a i) :
    groupOrder a = baselineMass q m + ∑ i, (a i - base q) := by
  have sum : (∑ i, a i) = (m + 1) * base q + ∑ i, (a i - base q) := by
    calc
      _ = ∑ i, (base q + (a i - base q)) :=
        Finset.sum_congr rfl (fun i _ => (Nat.add_sub_of_le (lower i)).symm)
      _ = _ := by simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_option, Fintype.card_fin, smul_eq_mul]
  unfold groupOrder baselineMass
  omega

theorem baselineGroups_order : groupOrder (baselineGroups q m) = baselineMass q m + 1 := by
  simp [groupOrder, baselineGroups, baselineMass, Fintype.sum_option]
  ring

theorem Instance.baselineGroups_equation :
    (∑ i, I.coefficient i * baselineGroups q m i) = I.weightedTarget := by
  apply (I.shifted_equation_iff _ (fun i => by cases i <;> simp [baselineGroups])).mpr
  rw [I.option_equation_iff]
  simpa only [baselineGroups, Nat.add_sub_cancel_left, Nat.sub_self] using I.baseline_solution

theorem Instance.coverGroups_equation (chosen : Finset (Fin m)) (cover : I.IsExactCover chosen) :
    (∑ i, I.coefficient i * coverGroups q m chosen i) = I.weightedTarget := by
  apply (I.shifted_equation_iff _ (fun i => by cases i <;> simp [coverGroups])).mpr
  rw [I.option_equation_iff]
  simpa only [coverGroups, Nat.add_sub_cancel_left, Nat.sub_self] using I.solution_of_exactCover chosen cover

theorem Instance.coverGroups_order (chosen : Finset (Fin m)) (cover : I.IsExactCover chosen) :
    groupOrder (coverGroups q m chosen) = baselineMass q m + q := by
  unfold groupOrder coverGroups
  rw [Fintype.sum_option]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter, Nat.cast_id]
  rw [Instance.IsExactCover.card_eq I cover]
  unfold baselineMass
  ring

/-- The shifted equation used for physical group sizes has exactly the
baseline allocation or an allocation from an exact cover. -/
theorem Instance.shifted_equation_classification (large : 2 ≤ q)
    (a : Option (Fin m) → ℕ) (lower : ∀ i, base q ≤ a i)
    (equation : (∑ i, I.coefficient i * a i) = I.weightedTarget) :
    a = baselineGroups q m ∨ ∃ chosen, I.IsExactCover chosen ∧ a = coverGroups q m chosen := by
  have targetEquation := (I.shifted_equation_iff a lower).mp equation
  have solution := (I.option_equation_iff _).mp targetEquation
  rcases (I.solution_iff large _ _).mp solution with ⟨head, tail⟩ | ⟨head, chosen, cover, tail⟩
  · left
    funext i
    cases i with
    | none => change a none = base q + 1; have := lower none; omega
    | some j => change a (some j) = base q; have := lower (some j); have := tail j; omega
  · right
    refine ⟨chosen, cover, ?_⟩
    funext i
    cases i with
    | none => change a none = base q; have := lower none; omega
    | some j =>
        change a (some j) = base q + if j ∈ chosen then 1 else 0
        have := lower (some j)
        have := tail j
        omega

theorem Instance.shifted_order_dichotomy (large : 2 ≤ q)
    (a : Option (Fin m) → ℕ) (lower : ∀ i, base q ≤ a i)
    (equation : (∑ i, I.coefficient i * a i) = I.weightedTarget) :
    groupOrder a = baselineMass q m + 1 ∨
      (groupOrder a = baselineMass q m + q ∧ ∃ chosen, I.IsExactCover chosen) := by
  rcases I.shifted_equation_classification large a lower equation with baseline | ⟨chosen, cover, alternate⟩
  · exact Or.inl (baseline ▸ baselineGroups_order)
  · exact Or.inr ⟨alternate ▸ I.coverGroups_order chosen cover, chosen, cover⟩

theorem Instance.alternate_order_iff_exactCover (large : 2 ≤ q) :
    (∃ a : Option (Fin m) → ℕ, (∀ i, base q ≤ a i) ∧
      (∑ i, I.coefficient i * a i) = I.weightedTarget ∧
      groupOrder a ≠ baselineMass q m + 1) ↔ ∃ chosen, I.IsExactCover chosen := by
  constructor
  · rintro ⟨a, lower, equation, different⟩
    rcases I.shifted_order_dichotomy large a lower equation with baseline | alternate
    · exact (different baseline).elim
    · exact alternate.2
  · rintro ⟨chosen, cover⟩
    refine ⟨coverGroups q m chosen, ?_, I.coverGroups_equation chosen cover, ?_⟩
    · intro i
      cases i <;> simp [coverGroups]
    · rw [I.coverGroups_order chosen cover]
      omega

end Counting.X3C
