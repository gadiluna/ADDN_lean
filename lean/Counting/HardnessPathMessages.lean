import Counting.HardnessPathGraph

namespace Counting.HardnessPath

variable {I : Type} [Fintype I]

omit [Fintype I] in
theorem member_ext (size : I → Nat) (a b : Member size)
    (group : a.1 = b.1) (position : a.2.val = b.2.val) : a = b := by
  obtain ⟨i, k⟩ := a
  obtain ⟨j, l⟩ := b
  dsimp at group position
  subst j
  have eq : k = l := Fin.ext position
  cases eq
  rfl

omit [Fintype I] in
theorem next_some_iff (size : I → Nat) (a b : Member size) :
    next size a = some b ↔ a.1 = b.1 ∧ a.2.val + 1 = b.2.val := by
  constructor
  · intro eq
    unfold next at eq
    split at eq
    · have same := Option.some.inj eq
      have group := congrArg (fun x : Member size => x.1) same
      have position := congrArg (fun x : Member size => x.2.val) same
      exact ⟨group, position⟩
    · cases eq
  · rintro ⟨group, position⟩
    have within : a.2.val + 1 < size a.1 := by
      rw [position, group]
      exact b.2.isLt
    simp only [next, dif_pos within]
    congr 1
    exact member_ext size _ b group position

omit [Fintype I] in
theorem next_unique_predecessor (size : I → Nat) (i : I) (j l : Fin (size i))
    (consecutive : j.val + 1 = l.val) (a : Member size) :
    next size a = some ⟨i, l⟩ ↔ a = ⟨i, j⟩ := by
  rw [next_some_iff]
  constructor
  · rintro ⟨group, position⟩
    exact member_ext size a ⟨i, j⟩ group (by dsimp at position ⊢; omega)
  · rintro rfl
    exact ⟨rfl, consecutive⟩

theorem incoming_first {S : Type} (coeff size : I → Nat) (state : Agent size → S)
    (i : I) (first : Fin (size i)) (zero : first.val = 0) :
    incoming (edge coeff size) state (some ⟨i, first⟩) = Multiset.replicate (coeff i) (state none) := by
  classical
  unfold incoming
  rw [Fintype.sum_option]
  have noPred (a : Member size) : next size a ≠ some ⟨i, first⟩ := by
    intro eq
    have h := (next_some_iff size a ⟨i, first⟩).mp eq
    dsimp at h
    omega
  simp only [edge, noPred, if_false, Multiset.replicate_zero, Finset.sum_const_zero, add_zero]

theorem incoming_next {S : Type} (coeff size : I → Nat) (state : Agent size → S)
    (i : I) (j l : Fin (size i)) (consecutive : j.val + 1 = l.val) :
    incoming (edge coeff size) state (some ⟨i, l⟩) =
      Multiset.replicate (coeff i) (state none) + {state (some ⟨i, j⟩)} := by
  classical
  unfold incoming
  rw [Fintype.sum_option]
  change Multiset.replicate (coeff i) (state none) + _ = _
  congr 1
  calc
    _ = ∑ a : Member size, if a = ⟨i, j⟩ then ({state (some a)} : Multiset S) else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      simp only [edge, next_unique_predecessor size i j l consecutive a]
      split_ifs <;> simp
    _ = _ := by simp

def last (size : I → Nat) (positive : ∀ i, 0 < size i) (i : I) : Fin (size i) :=
  ⟨size i - 1, by have := positive i; omega⟩

theorem incoming_leader {S : Type} (coeff size : I → Nat) (positive : ∀ i, 0 < size i)
    (state : Agent size → S) :
    incoming (edge coeff size) state none = ∑ i : I, ({state (some ⟨i, last size positive i⟩)} : Multiset S) := by
  classical
  unfold incoming
  rw [Fintype.sum_option]
  change Multiset.replicate 0 (state none) + _ = _
  rw [Multiset.replicate_zero, zero_add, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _
  have eqLast (j : Fin (size i)) : next size ⟨i, j⟩ = none ↔ j = last size positive i := by
    rw [next_none_iff]
    change j.val + 1 = size i ↔ j = last size positive i
    constructor
    · intro eq
      apply Fin.ext
      dsimp [last]
      omega
    · rintro rfl
      dsimp [last]
      have := positive i
      omega
  calc
    _ = ∑ j : Fin (size i), if j = last size positive i then
        ({state (some ⟨i, j⟩)} : Multiset S) else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      simp only [edge, eqLast]
      split_ifs <;> simp
    _ = _ := by simp

theorem star_incoming_member {S : Type} (coeff size : I → Nat) (state : Agent size → S)
    (a : Member size) :
    incoming (star coeff size) state (some a) = Multiset.replicate (coeff a.1) (state none) := by
  classical
  simp [incoming, Fintype.sum_option, star]

theorem star_incoming_leader {S : Type} (coeff size : I → Nat) (state : Agent size → S) :
    incoming (star coeff size) state none = ∑ a : Member size, ({state (some a)} : Multiset S) := by
  classical
  simp [incoming, Fintype.sum_option, star]

end Counting.HardnessPath
