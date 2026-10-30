import Counting.X3CInstance

namespace Counting.X3C

variable {q m : ℕ} (I : Instance q m)

def Instance.Solution (x₀ : ℕ) (x : Fin m → ℕ) : Prop :=
  target q * x₀ + ∑ j : Fin m, I.coefficient (some j) * x j = target q

def Instance.coverDigit (x : Fin m → ℕ) (e : Fin (3 * q)) : ℕ :=
  ∑ j : Fin m, if e ∈ I.triples j then x j else 0

theorem Instance.coverDigit_le_total (x : Fin m → ℕ) (e : Fin (3 * q)) :
    I.coverDigit x e ≤ ∑ j, x j := by
  apply Finset.sum_le_sum
  intro j _
  split <;> omega

theorem Instance.weighted_sum (x : Fin m → ℕ) :
    (∑ j : Fin m, I.coefficient (some j) * x j) =
      high q * (∑ j, x j) + digitValue (base q) (I.coverDigit x) := by
  classical
  unfold Instance.coefficient
  simp only [Nat.add_mul, Finset.sum_add_distrib, ← Finset.mul_sum]
  congr 1
  unfold digitValue Instance.coverDigit
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Instance.tripleValue, Finset.sum_mul]
  simp only [ite_mul, Nat.zero_mul]
  rw [← Finset.sum_filter]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
  apply Finset.sum_congr rfl
  intro e _
  exact Nat.mul_comm _ _

theorem Instance.coverDigit_total (x : Fin m → ℕ) :
    (∑ e : Fin (3 * q), I.coverDigit x e) = 3 * ∑ j, x j := by
  classical
  unfold Instance.coverDigit
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Finset.sum_filter]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.sum_const,
    smul_eq_mul, I.triple_card]

theorem Instance.Solution.coordinate_sum_le {x₀ : ℕ} {x : Fin m → ℕ}
    (large : 2 ≤ q) (solution : I.Solution x₀ x) : x₀ + (∑ j, x j) ≤ q := by
  have lower : high q * (x₀ + ∑ j, x j) ≤ target q := by
    rw [Nat.mul_add, Finset.mul_sum]
    calc
      _ ≤ target q * x₀ + ∑ j, I.coefficient (some j) * x j := by
        apply Nat.add_le_add
        · exact Nat.mul_le_mul_right x₀ (Nat.le_of_lt (target_gt_high q large))
        · exact Finset.sum_le_sum (fun j _ => Nat.mul_le_mul_right (x j)
            (Nat.le_of_lt (I.coefficient_gt_high large (some j))))
      _ = _ := solution
  have upper := target_lt q
  have positive := high_positive q
  nlinarith

theorem Instance.Solution.baseline_coordinate_le_one {x₀ : ℕ} {x : Fin m → ℕ}
    (large : 2 ≤ q) (solution : I.Solution x₀ x) : x₀ ≤ 1 := by
  have positive := target_positive q (by omega)
  unfold Instance.Solution at solution
  have lower : target q * x₀ ≤ target q := by omega
  nlinarith only [lower, positive]

theorem Instance.Solution.baseline_zeros {x : Fin m → ℕ}
    (large : 2 ≤ q) (solution : I.Solution 1 x) : ∀ j, x j = 0 := by
  have total : (∑ j, I.coefficient (some j) * x j) = 0 := by
    unfold Instance.Solution at solution
    omega
  intro j
  have term := Finset.single_le_sum (f := fun j => I.coefficient (some j) * x j)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  have positive := I.coefficient_positive large (some j)
  rw [total] at term
  nlinarith

theorem Instance.Solution.digits_exact {x : Fin m → ℕ}
    (large : 2 ≤ q) (solution : I.Solution 0 x) :
    (∑ j, x j) = q ∧ ∀ e, I.coverDigit x e = 1 := by
  have count := Instance.Solution.coordinate_sum_le I large solution
  have bounded : ∀ e, I.coverDigit x e < base q := by
    intro e
    have := I.coverDigit_le_total x e
    unfold base
    omega
  have eq : (∑ j, x j) * base q ^ (3 * q) + digitValue (base q) (I.coverDigit x) =
      q * base q ^ (3 * q) + digitValue (base q) (fun _ : Fin (3 * q) => 1) := by
    have sums := I.weighted_sum x
    unfold Instance.Solution at solution
    simp only [Nat.mul_zero, Nat.zero_add] at solution
    rw [sums] at solution
    simpa only [target, ones, high, Nat.mul_comm] using solution
  have digits := high_digit_unique (base q) (3 * q) (base_gt_one q)
    (I.coverDigit x) (fun _ => 1) bounded (fun _ => base_gt_one q) _ q eq
  exact ⟨digits.1, fun e => congrFun digits.2 e⟩

theorem Instance.coordinates_binary (x : Fin m → ℕ) (digits : ∀ e, I.coverDigit x e = 1) :
    ∀ j, x j = 0 ∨ x j = 1 := by
  intro j
  have nonempty : (I.triples j).Nonempty := Finset.card_pos.mp (by rw [I.triple_card]; decide)
  obtain ⟨e, he⟩ := nonempty
  have term := Finset.single_le_sum (f := fun j => if e ∈ I.triples j then x j else 0)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  change (if e ∈ I.triples j then x j else 0) ≤ I.coverDigit x e at term
  rw [if_pos he, digits e] at term
  omega

def selected (x : Fin m → ℕ) : Finset (Fin m) := Finset.univ.filter (fun j => x j = 1)

theorem selected_indicator (x : Fin m → ℕ) (binary : ∀ j, x j = 0 ∨ x j = 1) (j : Fin m) :
    x j = if j ∈ selected x then 1 else 0 := by
  rcases binary j with zero | one <;> simp_all [selected]

theorem Instance.coverDigit_indicator (chosen : Finset (Fin m)) (e : Fin (3 * q)) :
    I.coverDigit (fun j => if j ∈ chosen then 1 else 0) e =
      (chosen.filter (fun j => e ∈ I.triples j)).card := by
  classical
  unfold Instance.coverDigit
  calc
    _ = ∑ j : Fin m, if j ∈ chosen ∧ e ∈ I.triples j then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases first : j ∈ chosen <;> by_cases second : e ∈ I.triples j <;> simp [first, second]
    _ = _ := by
      simp only [Finset.sum_boole, Nat.cast_id]
      congr 1
      ext j
      simp

theorem Instance.exactCover_of_digits (x : Fin m → ℕ) (digits : ∀ e, I.coverDigit x e = 1) :
    I.IsExactCover (selected x) := by
  intro e
  rw [← I.coverDigit_indicator]
  have eq : (fun j => if j ∈ selected x then 1 else 0) = x :=
    funext (fun j => (selected_indicator x (I.coordinates_binary x digits) j).symm)
  rw [eq, digits e]

theorem Instance.solution_of_exactCover (chosen : Finset (Fin m)) (cover : I.IsExactCover chosen) :
    I.Solution 0 (fun j => if j ∈ chosen then 1 else 0) := by
  let x : Fin m → ℕ := fun j => if j ∈ chosen then 1 else 0
  have digits : ∀ e, I.coverDigit x e = 1 := fun e => (I.coverDigit_indicator chosen e).trans (cover e)
  have total := I.coverDigit_total x
  simp only [digits, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, Nat.mul_one] at total
  have count : (∑ j, x j) = q := by omega
  unfold Instance.Solution
  simp only [Nat.mul_zero, Nat.zero_add]
  rw [I.weighted_sum, count]
  change high q * q + digitValue (base q) (I.coverDigit x) = q * high q + ones q
  rw [show I.coverDigit x = (fun _ => 1) from funext digits]
  unfold ones
  rw [Nat.mul_comm]

theorem Instance.baseline_solution : I.Solution 1 (fun _ => 0) := by
  simp [Instance.Solution]

theorem Instance.IsExactCover.card_eq {chosen : Finset (Fin m)} (cover : I.IsExactCover chosen) :
    chosen.card = q := by
  have digits : ∀ e, I.coverDigit (fun j => if j ∈ chosen then 1 else 0) e = 1 :=
    fun e => (I.coverDigit_indicator chosen e).trans (cover e)
  have total := I.coverDigit_total (fun j => if j ∈ chosen then 1 else 0)
  simp only [digits, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
    Nat.mul_one, Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter, Nat.cast_id] at total
  omega

/-- The paper's exact equation: its only possibilities are the baseline
and zero-one coordinates selecting an exact cover of the explicit universe. -/
theorem Instance.solution_iff (large : 2 ≤ q) (x₀ : ℕ) (x : Fin m → ℕ) :
    I.Solution x₀ x ↔ (x₀ = 1 ∧ ∀ j, x j = 0) ∨
      (x₀ = 0 ∧ ∃ chosen, I.IsExactCover chosen ∧ ∀ j, x j = if j ∈ chosen then 1 else 0) := by
  constructor
  · intro solution
    have bound := Instance.Solution.baseline_coordinate_le_one I large solution
    by_cases zero : x₀ = 0
    · right
      subst x₀
      have digits := Instance.Solution.digits_exact I large solution
      exact ⟨rfl, selected x, I.exactCover_of_digits x digits.2,
        selected_indicator x (I.coordinates_binary x digits.2)⟩
    · left
      have one : x₀ = 1 := by omega
      exact ⟨one, Instance.Solution.baseline_zeros I large (one ▸ solution)⟩
  · rintro (⟨rfl, zero⟩ | ⟨rfl, chosen, cover, values⟩)
    · have eq : x = fun _ => 0 := funext zero
      rw [eq]
      exact I.baseline_solution
    · have eq : x = fun j => if j ∈ chosen then 1 else 0 := funext values
      rw [eq]
      exact I.solution_of_exactCover chosen cover

theorem Instance.option_equation_iff (x : Option (Fin m) → ℕ) :
    (∑ i, I.coefficient i * x i) = target q ↔ I.Solution (x none) (fun j => x (some j)) := by
  rw [Fintype.sum_option]
  rfl

theorem Instance.option_coordinate_sum_le (large : 2 ≤ q) (x : Option (Fin m) → ℕ)
    (solution : (∑ i, I.coefficient i * x i) = target q) : (∑ i, x i) ≤ q := by
  rw [Fintype.sum_option]
  exact Instance.Solution.coordinate_sum_le I large ((I.option_equation_iff x).mp solution)

theorem Instance.nonbaseline_solution_iff_exactCover (large : 2 ≤ q) :
    (∃ x : Option (Fin m) → ℕ, (∑ i, I.coefficient i * x i) = target q ∧ x none = 0) ↔
      ∃ chosen, I.IsExactCover chosen := by
  constructor
  · rintro ⟨x, equation, zero⟩
    have solution := (I.option_equation_iff x).mp equation
    rw [zero] at solution
    have digits := Instance.Solution.digits_exact I large solution
    exact ⟨selected (fun j => x (some j)), I.exactCover_of_digits _ digits.2⟩
  · rintro ⟨chosen, cover⟩
    let x : Option (Fin m) → ℕ := fun i => i.elim 0 (fun j => if j ∈ chosen then 1 else 0)
    refine ⟨x, (I.option_equation_iff x).mpr ?_, rfl⟩
    exact I.solution_of_exactCover chosen cover

end Counting.X3C
