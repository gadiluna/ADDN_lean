import Counting.Network
import Mathlib.Data.Fintype.BigOperators

/-! The repeated path graph and ordinary star of the coNP-hardness
construction. Group sizes are explicit; every natural multiplicity is
retained without expanding parallel arcs. -/

namespace Counting.HardnessPath
open DirectedCounting Relation

variable {I : Type} [Fintype I]

abbrev Member (size : I → Nat) := Σ i : I, Fin (size i)
abbrev Agent (size : I → Nat) := Option (Member size)

def leader (size : I → Nat) : Agent size → Bool
  | none => true
  | some _ => false

/-- The last member sends to the unique leader, all others to their next
member. Positions are zero-based in Lean and one-based in the paper. -/
def next (size : I → Nat) (a : Member size) : Agent size :=
  if h : a.2.val + 1 < size a.1 then some ⟨a.1, ⟨a.2.val + 1, h⟩⟩ else none

noncomputable def edge (coeff size : I → Nat) : Agent size → Agent size → Nat := by
  classical
  exact fun a b => match a, b with
    | none, none => 0
    | none, some b => coeff b.1
    | some a, b => if next size a = b then 1 else 0

noncomputable def star (coeff size : I → Nat) : Agent size → Agent size → Nat := by
  classical
  exact fun a b => match a, b with
    | none, none => 0
    | none, some b => coeff b.1
    | some _, none => 1
    | some _, some _ => 0

theorem population (size : I → Nat) : Fintype.card (Agent size) = 1 + ∑ i : I, size i := by
  simp [Agent, Member, Fintype.card_sigma, Nat.add_comm]

theorem leaders (size : I → Nat) : leaderCount (leader size) = 1 := by
  classical
  unfold leaderCount
  rw [Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_option]
  simp [leader]

omit [Fintype I] in
theorem next_none_iff (size : I → Nat) (a : Member size) :
    next size a = none ↔ a.2.val + 1 = size a.1 := by
  unfold next
  split
  · have := a.2.isLt
    simp only [Option.some_ne_none, false_iff]
    omega
  · have := a.2.isLt
    simp only [true_iff]
    omega

omit [Fintype I] in
theorem next_ne_self (size : I → Nat) (a : Member size) : next size a ≠ some a := by
  intro eq
  unfold next at eq
  split at eq
  · have pair := Option.some.inj eq
    have idx := congrArg (fun x : Member size => x.2.val) pair
    dsimp at idx
    omega
  · cases eq

omit [Fintype I] in
theorem path_loopless (coeff size : I → Nat) (a : Agent size) : edge coeff size a a = 0 := by
  classical
  cases a with
  | none => rfl
  | some a => exact if_neg (next_ne_self size a)

omit [Fintype I] in
theorem star_loopless (coeff size : I → Nat) (a : Agent size) : star coeff size a a = 0 := by
  cases a <;> rfl

theorem member_outdegree (coeff size : I → Nat) (a : Member size) :
    (∑ b : Agent size, edge coeff size (some a) b) = 1 := by
  classical
  simp [edge]

theorem leader_outdegree (coeff size : I → Nat) :
    (∑ b : Agent size, edge coeff size none b) = ∑ i : I, coeff i * size i := by
  classical
  rw [Fintype.sum_option]
  change 0 + (∑ b : Member size, coeff b.1) = _
  rw [Nat.zero_add, Fintype.sum_sigma]
  simp [Nat.mul_comm]

theorem star_member_outdegree (coeff size : I → Nat) (a : Member size) :
    (∑ b : Agent size, star coeff size (some a) b) = 1 := by
  classical
  simp [Fintype.sum_option, star]

theorem star_leader_outdegree (coeff size : I → Nat) :
    (∑ b : Agent size, star coeff size none b) = ∑ i : I, coeff i * size i := by
  simpa [edge, star, Fintype.sum_option] using leader_outdegree coeff size

omit [Fintype I] in
theorem consecutive_edge (coeff size : I → Nat) (i : I)
    (k l : Fin (size i)) (consecutive : k.val + 1 = l.val) :
    edge coeff size (some ⟨i, k⟩) (some ⟨i, l⟩) = 1 := by
  classical
  have hl : k.val + 1 < size i := consecutive ▸ l.isLt
  have eq : next size ⟨i, k⟩ = some ⟨i, l⟩ := by
    simp only [next, dif_pos hl]
    congr 2
    exact Fin.ext consecutive
  simp only [edge, eq, if_true]

omit [Fintype I] in
theorem to_leader (coeff size : I → Nat) (a : Member size) :
    ReflTransGen (fun x y => 0 < edge coeff size x y) (some a) none := by
  obtain ⟨i, k⟩ := a
  let P (j : Fin (size i)) := ReflTransGen (fun x y => 0 < edge coeff size x y) (some ⟨i, j⟩) none
  have h : ∀ d, ∀ j : Fin (size i), size i - j.val = d → P j := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro j distance
      by_cases last : j.val + 1 = size i
      · exact .single (by simp [edge, (next_none_iff size ⟨i, j⟩).mpr last])
      · have hj : j.val + 1 < size i := by have := j.isLt; omega
        let nextJ : Fin (size i) := ⟨j.val + 1, hj⟩
        have smaller : size i - nextJ.val < d := by dsimp [nextJ]; have := j.isLt; omega
        have rest := ih (size i - nextJ.val) smaller nextJ rfl
        exact rest.head (by rw [consecutive_edge coeff size i j nextJ rfl]; omega)
  exact h _ k rfl

omit [Fintype I] in
theorem path_connected (coeff size : I → Nat) (positive : ∀ i, 0 < coeff i) :
    StronglyConnected (fun a b => 0 < edge coeff size a b) := by
  have first (a : Agent size) : ReflTransGen (fun x y => 0 < edge coeff size x y) a none := by
    cases a with
    | none => exact .refl
    | some a => exact to_leader coeff size a
  have last (b : Agent size) : ReflTransGen (fun x y => 0 < edge coeff size x y) none b := by
    cases b with
    | none => exact .refl
    | some b => exact .single (positive b.1)
  exact fun a b => (first a).trans (last b)

omit [Fintype I] in
theorem star_connected (coeff size : I → Nat) (positive : ∀ i, 0 < coeff i) :
    StronglyConnected (fun a b => 0 < star coeff size a b) := by
  intro a b
  have first : ReflTransGen (fun x y => 0 < star coeff size x y) a none := by
    cases a
    · exact .refl
    · exact .single (by simp [star])
  have last : ReflTransGen (fun x y => 0 < star coeff size x y) none b := by
    cases b with
    | none => exact .refl
    | some b => exact .single (positive b.1)
  exact first.trans last

end Counting.HardnessPath
