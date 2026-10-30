import Counting.RealizabilityConstructionHistory

/-! A round normalization preserving all visible columns and visible degrees.
Hidden agents communicate through a chosen hidden agent. -/
namespace Counting.SmallPrefix
open DirectedCounting Relation
variable {A : Type} [Fintype A] [DecidableEq A]

def kept (E : A → A → Nat) (S : Finset A) (a : A) : Nat :=
  ∑ b, if b ∈ S then E a b else 0

def lost (E : A → A → Nat) (S : Finset A) (a : A) : Nat :=
  ∑ b, if b ∈ S then 0 else E a b

theorem kept_add_lost (E : A → A → Nat) (S : Finset A) (a : A) :
    kept E S a + lost E S a = ∑ b, E a b := by
  rw [kept, lost, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b _
  split_ifs <;> simp

def normalize (E : A → A → Nat) (S : Finset A) (q : A) (D : Nat) (a b : A) : Nat :=
  if b ∈ S then E a b else
  if a = q then (if b = q then D + 1 else 1) else
  if b = q then (if a ∈ S then lost E S a else D - kept E S a) else 0

theorem normalize_visible (E : A → A → Nat) (S : Finset A) (q : A) (D : Nat)
    (a b : A) (visible : b ∈ S) : normalize E S q D a b = E a b := by
  simp [normalize, visible]

theorem normalize_row (E : A → A → Nat) (S : Finset A) (q : A) (D : Nat)
    (outside : q ∉ S) (a : A) (different : a ≠ q) :
    (∑ b, normalize E S q D a b) =
      kept E S a + if a ∈ S then lost E S a else D - kept E S a := by
  have point (b : A) : normalize E S q D a b =
      (if b ∈ S then E a b else 0) +
      (if b = q then (if a ∈ S then lost E S a else D - kept E S a) else 0) := by
    by_cases eq : b = q
    · subst b; simp [normalize, outside, different]
    · simp [normalize, eq, different]
  simp_rw [point]
  rw [Finset.sum_add_distrib]
  simp [kept]

theorem normalize_visible_degree (E : A → A → Nat) (S : Finset A) (q : A) (D : Nat)
    (outside : q ∉ S) (a : A) (visible : a ∈ S) :
    (∑ b, normalize E S q D a b) = ∑ b, E a b := by
  have different : a ≠ q := by intro eq; exact outside (eq ▸ visible)
  rw [normalize_row E S q D outside a different, if_pos visible, kept_add_lost]

theorem normalize_hidden_degree (E : A → A → Nat) (S : Finset A) (q : A) (D : Nat)
    (outside : q ∉ S) (a : A) (hidden : a ∉ S) (different : a ≠ q)
    (bound : kept E S a ≤ D) : (∑ b, normalize E S q D a b) = D := by
  rw [normalize_row E S q D outside a different, if_neg hidden]
  omega

theorem normalize_hidden_column (E : A → A → Nat) (S : Finset A) (q : A) (D : Nat)
    (b : A) (hidden : b ∉ S) (different : b ≠ q) (a : A) :
    normalize E S q D a b = if a = q then 1 else 0 := by
  simp [normalize, hidden, different]

theorem normalize_hidden_incoming {B : Type} (E : A → A → Nat) (S : Finset A)
    (q : A) (D : Nat) (state : A → B) (b : A) (hidden : b ∉ S) (different : b ≠ q) :
    incoming (normalize E S q D) state b = {state q} := by
  classical
  apply Multiset.ext.mpr
  intro h
  rw [count_incoming]
  simp_rw [normalize_hidden_column E S q D b hidden different]
  have point (a : A) : (if state a = h then (if a = q then 1 else 0) else 0) =
      if a = q then (if state q = h then 1 else 0) else 0 := by
    by_cases eq : a = q <;> simp [eq]
  simp_rw [point]
  simp [Multiset.count_singleton, eq_comm]

theorem normalize_connected (E : A → A → Nat) (S : Finset A) (q : A) (D : Nat)
    (outside : q ∉ S) (bound : ∀ a, kept E S a < D)
    (connected : StronglyConnected (fun a b => 0 < E a b)) :
    StronglyConnected (fun a b => 0 < normalize E S q D a b) := by
  have toHub (a : A) (hidden : a ∉ S) :
      ReflTransGen (fun x y => 0 < normalize E S q D x y) a q := by
    by_cases eq : a = q
    · subst a; exact .refl
    · exact .single (by simp [normalize, outside, eq, hidden, bound a])
  have fromHub (b : A) (hidden : b ∉ S) :
      ReflTransGen (fun x y => 0 < normalize E S q D x y) q b := by
    by_cases eq : b = q
    · subst b; exact .refl
    · exact .single (by simp [normalize, hidden, eq])
  have lift (a b : A) (edge : 0 < E a b) :
      ReflTransGen (fun x y => 0 < normalize E S q D x y) a b := by
    by_cases target : b ∈ S
    · exact .single (by simpa [normalize, target] using edge)
    · by_cases source : a ∈ S
      · have different : a ≠ q := fun eq => outside (eq ▸ source)
        have positive : 0 < lost E S a :=
          Finset.sum_pos_iff.mpr ⟨b, Finset.mem_univ b, by simpa [target] using edge⟩
        have first : 0 < normalize E S q D a q := by
          simpa [normalize, outside, different, source] using positive
        exact (fromHub b target).head first
      · exact (toHub a source).trans (fromHub b target)
  intro a b
  have path := connected a b
  induction path with
  | refl => exact .refl
  | tail _ edge ih => exact ih.trans (lift _ _ edge)

theorem normalize_hub_degree_le (E : A → A → Nat) (S : Finset A) (q : A) (D : Nat)
    (outside : q ∉ S) :
    (∑ b, normalize E S q D q b) ≤ kept E S q + Fintype.card A + D + 1 := by
  have point (b : A) : normalize E S q D q b ≤
      (if b ∈ S then E q b else 0) + 1 + (if b = q then D else 0) := by
    by_cases eq : b = q
    · subst b; simp [normalize, outside]
    · simp [normalize, eq]; split_ifs <;> omega
  have h := Finset.sum_le_sum (fun b (_ : b ∈ (Finset.univ : Finset A)) => point b)
  have h' : (∑ b, normalize E S q D q b) ≤ kept E S q + Fintype.card A + D := by
    simpa [Finset.sum_add_distrib, kept, Nat.add_assoc] using h
  omega

end Counting.SmallPrefix
