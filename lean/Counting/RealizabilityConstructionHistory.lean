import Counting.VistaIsomorphismActual

/-! Reconstructing actual histories from per-round selected-type receipts.
Unselected agents may share selected histories: their zero incoming
contribution is explicitly used rather than assuming such histories differ.
-/

namespace Counting.RealizabilityConstruction
open DirectedCounting

variable {A : Type} [Fintype A]

noncomputable def taggedIncoming {C : Type} (edge : A → A → Nat)
    (tag : A → Option C) (c : C) (a : A) : Nat := by
  classical
  exact ∑ b : A, if tag b = some c then edge b a else 0

/-- Selected history labels need not label every physical agent. Exact
outdegrees, old-type receipts, and exclusion of previously unselected
senders suffice to reconstruct every prescribed selected history. -/
theorem selected_histories (G : Nat → A → A → Nat) (leader : A → Bool)
    (tag : ∀ r, A → Option (FullHistory r)) (t : Nat)
    (initial : ∀ a h, tag 0 a = some h → leader a = h)
    (nested : ∀ r, r < t → ∀ a (v : FullHistory (r + 1)),
      tag (r + 1) a = some v → tag r a = some v.1)
    (degrees : ∀ r, r < t → ∀ a (v : FullHistory (r + 1)),
      tag (r + 1) a = some v → (∑ b : A, G (r + 1) a b) = v.2.1)
    (receipts : ∀ r, r < t → ∀ a (v : FullHistory (r + 1)),
      tag (r + 1) a = some v → ∀ u : FullHistory r,
      taggedIncoming (G (r + 1)) (tag r) u a = v.2.2.count u)
    (exclude : ∀ r, r < t → ∀ a (v : FullHistory (r + 1)),
      tag (r + 1) a = some v → ∀ b, tag r b = none → G (r + 1) b a = 0) :
    ∀ r, r ≤ t → ∀ a h, tag r a = some h → history G leader r a = h := by
  classical
  intro r
  induction r with
  | zero => intro _ a h selected; exact initial a h selected
  | succ r ih =>
    intro bound a v selected
    have before : r < t := by omega
    apply Prod.ext (ih (by omega) a v.1 (nested r before a v selected))
    apply Prod.ext (degrees r before a v selected)
    apply Multiset.ext.mpr
    intro u
    change (incoming (G (r + 1)) (history G leader r) a).count u = _
    rw [count_incoming, ← receipts r before a v selected u]
    unfold taggedIncoming
    apply Finset.sum_congr rfl
    intro b _
    cases ht : tag r b with
    | none => simp [exclude r before a v selected b ht]
    | some w =>
      have hist := ih (by omega) b w ht
      simp only [hist, Option.some.injEq]

/-- Any finite prefix with strongly connected communication rounds extends
to an admissible infinite network without changing the prefix. -/
noncomputable def extendPrefix (t : Nat) (G : Nat → A → A → Nat) : Nat → A → A → Nat :=
  fun r a b => if r ≤ t then G r a b else 1

omit [Fintype A] in
theorem extendPrefix_eq (t : Nat) (G : Nat → A → A → Nat) (r : Nat) (within : r ≤ t) :
    extendPrefix t G r = G r := by
  funext a b
  simp only [extendPrefix, if_pos within]

theorem extendPrefix_history (t : Nat) (G : Nat → A → A → Nat) (leader : A → Bool)
    (r : Nat) (within : r ≤ t) (a : A) :
    history (extendPrefix t G) leader r a = history G leader r a := by
  induction r generalizing a with
  | zero => rfl
  | succ r ih =>
    have previous : history (extendPrefix t G) leader r = history G leader r :=
      funext (ih (by omega))
    simp only [history, extendPrefix_eq t G (r + 1) within, previous]

theorem extendPrefix_admissible (t : Nat) (G : Nat → A → A → Nat) (leader : A → Bool)
    (ell : Nat) (positive : 0 < ell) (leaders : leaderCount leader = ell)
    (connected : ∀ r, 0 < r → r ≤ t → StronglyConnected (fun a b => 0 < G r a b)) :
    Admissible ell (extendPrefix t G) leader where
  positive := positive
  leaders := leaders
  connected := by
    intro r hr
    by_cases within : r ≤ t
    · rw [extendPrefix_eq t G r within]
      exact connected r hr within
    · intro a b
      exact Relation.ReflTransGen.single (by simp [extendPrefix, within])

end Counting.RealizabilityConstruction
