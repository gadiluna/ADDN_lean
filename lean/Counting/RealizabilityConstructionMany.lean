import Counting.RealizabilityConstructionEliminate

/-!
# Eliminating finitely many independent balanced auxiliary vertices

Physical vertices are A and auxiliary vertices are U. Auxiliary vertices
have no arcs between one another. Every incoming arc at one auxiliary
vertex has its prescribed color, so removing all auxiliaries preserves
each color's receipts, as well as all physical outdegrees and strong
connectivity. A physical row that never enters an auxiliary stays intact.
-/

namespace Counting.RealizabilityConstruction
open DirectedCounting BalancedVertex
open scoped BigOperators

universe u v w
variable {A : Type u} {U : Type v} {C : Type w}

noncomputable def separateHub (z : U) : Option (A ⊕ {u : U // u ≠ z}) ≃ A ⊕ U := by
  classical
  exact {
    toFun := fun q => match q with
      | none => .inr z
      | some (.inl a) => .inl a
      | some (.inr u) => .inr u.val
    invFun := fun q => match q with
      | .inl a => some (.inl a)
      | .inr u => if h : u = z then none else some (.inr ⟨u, h⟩)
    left_inv := by
      intro q
      cases q with
      | none => simp
      | some q =>
        cases q with
        | inl a => rfl
        | inr u => simp [u.property]
    right_inv := by
      intro q
      cases q with
      | inl a => rfl
      | inr u => by_cases h : u = z <;> simp [h]
  }

@[simp] theorem separateHub_none (z : U) : separateHub (A := A) z none = .inr z := rfl
@[simp] theorem separateHub_physical (z : U) (a : A) : separateHub z (some (.inl a)) = .inl a := rfl
@[simp] theorem separateHub_auxiliary (z : U) (a : {u : U // u ≠ z}) :
    separateHub (A := A) z (some (.inr a)) = .inr a.val := rfl

theorem stronglyConnected_reindex {S T : Type*} (e : S ≃ T) (D : T → T → Nat)
    (connected : StronglyConnected (fun x y => 0 < D x y)) :
    StronglyConnected (fun x y => 0 < D (e x) (e y)) := by
  have mapped : ∀ a b, Relation.ReflTransGen (fun x y => 0 < D x y) a b →
      Relation.ReflTransGen (fun x y => 0 < D (e x) (e y)) (e.symm a) (e.symm b) := by
    intro a b path
    induction path with
    | refl => exact .refl
    | @tail a b _ edge ih => exact ih.tail (by simpa using edge)
  intro a b
  simpa using mapped (e a) (e b) (connected (e a) (e b))

structure ManyEliminated [Fintype A] [Fintype U] [DecidableEq C]
    (D : (A ⊕ U) → (A ⊕ U) → Nat) (color : A → C) (hub : U → C)
    (E : A → A → Nat) : Prop where
  connected : StronglyConnected (fun x y => 0 < E x y)
  outdegree : ∀ x, (∑ y : A, E x y) = ∑ y : A ⊕ U, D (.inl x) y
  colored : ∀ y c,
    (∑ x : A, if color x = c then E x y else 0) =
      (∑ x : A, if color x = c then D (.inl x) (.inl y) else 0) +
      ∑ u : U, if hub u = c then D (.inr u) (.inl y) else 0
  untouched : ∀ x, (∀ u, D (.inl x) (.inr u) = 0) → ∀ y, E x y = D (.inl x) (.inl y)

/-- Simultaneously eliminate an arbitrary finite independent family of
balanced auxiliary vertices, preserving all specified colored receipts. -/
theorem eliminate_many_colored [Fintype A] [Nonempty A] [Fintype U] [DecidableEq C]
    (D : (A ⊕ U) → (A ⊕ U) → Nat) (color : A → C) (hub : U → C)
    (independent : ∀ u v, D (.inr u) (.inr v) = 0)
    (balanced : ∀ u, (∑ x : A, D (.inl x) (.inr u)) = ∑ x : A, D (.inr u) (.inl x))
    (connected : StronglyConnected (fun x y => 0 < D x y))
    (tails : ∀ x u, 0 < D (.inl x) (.inr u) → color x = hub u) :
    ∃ E : A → A → Nat, ManyEliminated D color hub E := by
  classical
  have aux : ∀ n (U : Type v) [Fintype U], Fintype.card U = n →
      ∀ (D : (A ⊕ U) → (A ⊕ U) → Nat) (hub : U → C),
        (∀ u v, D (.inr u) (.inr v) = 0) →
        (∀ u, (∑ x : A, D (.inl x) (.inr u)) = ∑ x : A, D (.inr u) (.inl x)) →
        StronglyConnected (fun x y => 0 < D x y) →
        (∀ x u, 0 < D (.inl x) (.inr u) → color x = hub u) →
        ∃ E : A → A → Nat, ManyEliminated D color hub E := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro U finite order D hub independent balanced connected tails
      rcases isEmpty_or_nonempty U with empty | nonempty
      · letI : IsEmpty U := empty
        let E : A → A → Nat := fun x y => D (.inl x) (.inl y)
        have extract : ∀ x y : A ⊕ U, Relation.ReflTransGen (fun x y => 0 < D x y) x y →
            ∀ a b, x = .inl a → y = .inl b → Relation.ReflTransGen (fun a b => 0 < E a b) a b := by
          intro x y path
          induction path with
          | refl => intro a b ha hb; cases ha; cases hb; exact .refl
          | @tail x y _ edge hp =>
              intro a b ha hb
              cases x with
              | inl c => exact (hp a c ha rfl).tail (by cases hb; exact edge)
              | inr u => exact isEmptyElim u
        refine ⟨E, ?_⟩
        constructor
        · intro a b
          exact extract _ _ (connected (.inl a) (.inl b)) a b rfl rfl
        · intro x
          simp [Fintype.sum_sum_type, E]
        · intro y c
          simp [E]
        · intro x _ y
          rfl
      · letI : Nonempty U := nonempty
        let z : U := Classical.choice nonempty
        let R := {u : U // u ≠ z}
        let e : Option (A ⊕ R) ≃ A ⊕ U := separateHub z
        let D' : Option (A ⊕ R) → Option (A ⊕ R) → Nat := fun x y => D (e x) (e y)
        have loopless : D' none none = 0 := independent z z
        have balance : (∑ x : A ⊕ R, D' (some x) none) = ∑ x : A ⊕ R, D' none (some x) := by
          rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
          change (∑ x : A, D (.inl x) (.inr z)) + (∑ u : R, D (.inr u.val) (.inr z)) =
            (∑ x : A, D (.inr z) (.inl x)) + (∑ u : R, D (.inr z) (.inr u.val))
          simp only [independent, Finset.sum_const_zero, Nat.add_zero]
          exact balanced z
        have connected' : StronglyConnected (fun x y => 0 < D' x y) :=
          stronglyConnected_reindex e D connected
        obtain ⟨matching, connected₁⟩ := eliminate_balanced_vertex D' loopless balance connected'
        let D₁ : (A ⊕ R) → (A ⊕ R) → Nat := eliminate D' matching
        have row (u : R) (q : A ⊕ R) : D₁ (.inr u) q = D (.inr u.val) (e (some q)) :=
          eliminate_eq_of_no_incoming D' matching (.inr u) q (independent u.val z)
        have column (u : R) (q : A ⊕ R) : D₁ q (.inr u) = D (e (some q)) (.inr u.val) :=
          eliminate_eq_of_no_outgoing D' matching q (.inr u) (independent z u.val)
        have independent₁ : ∀ u v : R, D₁ (.inr u) (.inr v) = 0 := by
          intro u v
          exact (row u (.inr v)).trans (independent u.val v.val)
        have balanced₁ : ∀ u : R, (∑ x : A, D₁ (.inl x) (.inr u)) =
            ∑ x : A, D₁ (.inr u) (.inl x) := by
          intro u
          simp only [column, row]
          exact balanced u.val
        have tails₁ : ∀ x (u : R), 0 < D₁ (.inl x) (.inr u) → color x = hub u.val := by
          intro x u positive
          rw [column] at positive
          exact tails x u.val positive
        have smaller : Fintype.card R < n := by
          rw [← order]
          exact Fintype.card_subtype_lt (x := z) (by simp)
        obtain ⟨E, result⟩ := ih (Fintype.card R) smaller R rfl D₁ (fun u => hub u.val)
          independent₁ balanced₁ connected₁ tails₁
        refine ⟨E, ?_⟩
        constructor
        · exact result.connected
        · intro x
          calc
            (∑ y : A, E x y) = ∑ y : A ⊕ R, D₁ (.inl x) y := result.outdegree x
            _ = ∑ y : Option (A ⊕ R), D' (some (.inl x)) y := eliminate_outdegree D' matching (.inl x)
            _ = ∑ y : A ⊕ U, D (.inl x) y := e.sum_comp (fun y => D (.inl x) y)
        · intro y c
          let color₁ : A ⊕ R → C := Sum.elim color (fun u => hub u.val)
          have typed : ∀ q : A ⊕ R, 0 < D' (some q) none → color₁ q = hub z := by
            intro q positive
            cases q with
            | inl x => exact tails x z positive
            | inr u =>
                change 0 < D (.inr u.val) (.inr z) at positive
                rw [independent] at positive
                omega
          have receipts := eliminate_colored_incoming D' matching color₁ (hub z) typed (.inl y) c
          rw [Fintype.sum_sum_type, Fintype.sum_sum_type] at receipts
          change (∑ x : A, if color x = c then D₁ (.inl x) (.inl y) else 0) +
              (∑ u : R, if hub u.val = c then D₁ (.inr u) (.inl y) else 0) =
            ((∑ x : A, if color x = c then D (.inl x) (.inl y) else 0) +
              ∑ u : R, if hub u.val = c then D (.inr u.val) (.inl y) else 0) +
              if hub z = c then D (.inr z) (.inl y) else 0 at receipts
          rw [result.colored, receipts,
            Fintype.sum_eq_add_sum_subtype_ne (fun u => if hub u = c then D (.inr u) (.inl y) else 0) z]
          ac_rfl
        · intro x noAux y
          have noAux₁ : ∀ u : R, D₁ (.inl x) (.inr u) = 0 := by
            intro u
            exact (column u (.inl x)).trans (noAux u.val)
          exact (result.untouched x noAux₁ y).trans
            (eliminate_eq_of_no_incoming D' matching (.inl x) (.inl y) (noAux z))
  exact aux (Fintype.card U) U rfl D hub independent balanced connected tails

/-- The realization interface: auxiliary u has old selected type some u.
Unselected physical vertices (old=None) keep their entire outgoing row. -/
theorem eliminate_independent_auxiliaries [Fintype A] [Nonempty A] [Fintype U]
    [DecidableEq U] (D : (A ⊕ U) → (A ⊕ U) → Nat) (old : A → Option U)
    (independent : ∀ u v, D (.inr u) (.inr v) = 0)
    (balanced : ∀ u, (∑ x : A ⊕ U, D x (.inr u)) = ∑ x : A ⊕ U, D (.inr u) x)
    (connected : StronglyConnected (fun x y => 0 < D x y))
    (tails : ∀ x u, 0 < D (.inl x) (.inr u) → old x = some u) :
    ∃ E : A → A → Nat,
      StronglyConnected (fun x y => 0 < E x y) ∧
      (∀ x, (∑ y : A, E x y) = ∑ y : A ⊕ U, D (.inl x) y) ∧
      (∀ u y, (∑ x : A, if old x = some u then E x y else 0) =
        (∑ x : A, if old x = some u then D (.inl x) (.inl y) else 0) + D (.inr u) (.inl y)) ∧
      (∀ x, old x = none → ∀ y, E x y = D (.inl x) (.inl y)) := by
  classical
  have balance : ∀ u, (∑ x : A, D (.inl x) (.inr u)) = ∑ x : A, D (.inr u) (.inl x) := by
    intro u
    have h := balanced u
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type] at h
    simpa only [independent, Finset.sum_const_zero, Nat.add_zero] using h
  obtain ⟨E, result⟩ := eliminate_many_colored D old some independent balance connected tails
  refine ⟨E, result.connected, result.outdegree, ?_, ?_⟩
  · intro u y
    simpa using result.colored y (some u)
  · intro x unselected y
    apply result.untouched x _ y
    intro u
    by_contra nonzero
    have typed := tails x u (Nat.pos_of_ne_zero nonzero)
    rw [unselected] at typed
    cases typed

end Counting.RealizabilityConstruction
