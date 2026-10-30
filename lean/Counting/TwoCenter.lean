import Counting.Network

/-!
# Two-center graph construction

The two disjoint vertex sets are represented by the summands of `U ⊕ W`.
The edge function lists exactly the four bundles in Lemma `lem:two-center-graph`.
All incoming patterns below refer to previous states, as required by the
late-outdegree model.
-/

namespace Counting.TwoCenter

open DirectedCounting
open scoped BigOperators

variable {U W : Type} [Fintype U] [DecidableEq U] [DecidableEq W]

/-- The exact four bundles; `z` is the left center and `z'` the right center. -/
def edge (z : U) (z' : W) (c : Nat) : Sum U W → Sum U W → Nat
  | .inl u, .inl v => if u ≠ z ∧ v = z then Fintype.card U / c else 0
  | .inl u, .inr _ => if u = z then c else 0
  | .inr w, .inl u => if w = z' then 1 else if u = z then Fintype.card U else 0
  | .inr _, .inr _ => 0

def network (z : U) (z' : W) (c : Nat) : Nat → Sum U W → Sum U W → Nat :=
  fun _ ↦ edge z z' c

/-- The left summand contains precisely the leaders. -/
def leader : Sum U W → Bool
  | .inl _ => true
  | .inr _ => false

omit [DecidableEq U] in
lemma left_card_pos (z : U) : 0 < Fintype.card U :=
  Fintype.card_pos_iff.mpr ⟨z⟩

omit [DecidableEq U] in
lemma forward_bundle_pos (z : U) (c : Nat) (hc : c = 1 ∨ c = Fintype.card U) :
    0 < c := by
  rcases hc with rfl | rfl
  · omega
  · exact left_card_pos z

omit [DecidableEq U] in
lemma return_bundle_pos (z : U) (c : Nat) (hc : c = 1 ∨ c = Fintype.card U) :
    0 < Fintype.card U / c := by
  rcases hc with rfl | rfl
  · simpa using left_card_pos z
  · simp [left_card_pos z]

/-- No listed bundle creates a self-loop. -/
theorem loopless (z : U) (z' : W) (c : Nat) (v : Sum U W) :
    edge z z' c v v = 0 := by
  cases v with
  | inl u => simp [edge]
  | inr w => rfl

/-- Every noncenter agent has a direct positive arc to the left center. -/
theorem direct_to_center (z : U) (z' : W) (c : Nat)
    (hc : c = 1 ∨ c = Fintype.card U)
    (v : Sum U W) (hv : v ≠ .inl z) :
    0 < edge z z' c v (.inl z) := by
  cases v with
  | inl u =>
      have hu : u ≠ z := fun h ↦ hv (congrArg Sum.inl h)
      simpa [edge, hu] using return_bundle_pos z c hc
  | inr w =>
      by_cases hw : w = z'
      · simp [edge, hw]
      · simpa [edge, hw] using left_card_pos z

/-- The left center reaches every right vertex directly, and every left
vertex through the right center. -/
theorem center_reaches (z : U) (z' : W) (c : Nat)
    (hc : c = 1 ∨ c = Fintype.card U) (v : Sum U W) :
    Relation.ReflTransGen (fun u v ↦ 0 < edge z z' c u v) (.inl z) v := by
  have first : 0 < edge z z' c (.inl z) (.inr z') := by
    simpa [edge] using forward_bundle_pos z c hc
  cases v with
  | inl u =>
      have hp : Relation.ReflTransGen (fun u v ↦ 0 < edge z z' c u v)
          (.inl z) (.inr z') := .single first
      exact hp.tail (by simp [edge])
  | inr w =>
      exact Relation.ReflTransGen.single (by simpa [edge] using forward_bundle_pos z c hc)

/-- Strong connectivity for each allowed bundle multiplier. -/
theorem stronglyConnected (z : U) (z' : W) (c : Nat)
    (hc : c = 1 ∨ c = Fintype.card U) :
    StronglyConnected (fun u v ↦ 0 < edge z z' c u v) := by
  intro u v
  have first : Relation.ReflTransGen (fun u v ↦ 0 < edge z z' c u v) u (.inl z) := by
    by_cases hu : u = .inl z
    · subst u
      exact .refl
    · exact .single (direct_to_center z z' c hc u hu)
  exact first.trans (center_reaches z z' c hc v)

variable [Fintype W]

/-- An ordinary left vertex has only its return bundle to the left center. -/
theorem left_outdegree (z : U) (z' : W) (c : Nat) (u : U) (hu : u ≠ z) :
    (∑ v, edge z z' c (.inl u) v) = Fintype.card U / c := by
  rw [Fintype.sum_sum_type]
  simp [edge, hu]

/-- Every right vertex has total outdegree ell, including the right center. -/
theorem right_outdegree (z : U) (z' : W) (c : Nat) (w : W) :
    (∑ v, edge z z' c (.inr w) v) = Fintype.card U := by
  rw [Fintype.sum_sum_type]
  by_cases hw : w = z'
  · simp [edge, hw]
  · simp [edge, hw]

/-- The left center sends c copies to each right vertex. -/
theorem center_outdegree (z : U) (z' : W) (c : Nat) :
    (∑ v, edge z z' c (.inl z) v) = c * Fintype.card W := by
  rw [Fintype.sum_sum_type]
  simp [edge, Nat.mul_comm]

/-- Every ordinary left agent receives exactly one old state from the right center. -/
theorem left_incoming {State : Type} (z : U) (z' : W) (c : Nat)
    (state : Sum U W → State) (u : U) (hu : u ≠ z) :
    incoming (edge z z' c) state (.inl u) = {state (.inr z')} := by
  classical
  unfold incoming
  rw [Fintype.sum_sum_type]
  simp only [edge, hu, and_false, if_false, Multiset.replicate_zero,
    Finset.sum_const_zero, zero_add]
  calc
    _ = ∑ w : W, if w = z' then ({state (.inr w)} : Multiset State) else 0 := by
      apply Finset.sum_congr rfl
      intro w _
      split_ifs <;> simp
    _ = _ := by simp

/-- Every right agent receives exactly c copies of the left center's old state. -/
theorem right_incoming {State : Type} (z : U) (z' : W) (c : Nat)
    (state : Sum U W → State) (w : W) :
    incoming (edge z z' c) state (.inr w) =
      Multiset.replicate c (state (.inl z)) := by
  classical
  unfold incoming
  rw [Fintype.sum_sum_type]
  simp only [edge, Multiset.replicate_zero, Finset.sum_const_zero, add_zero]
  calc
    _ = ∑ u : U, if u = z then Multiset.replicate c (state (.inl u)) else 0 := by
      apply Finset.sum_congr rfl
      intro u _
      split_ifs <;> simp
    _ = _ := by simp

omit [DecidableEq U] [DecidableEq W] in
/-- The two summands make the leader count exactly ell. -/
theorem leader_count : Counting.leaderCount (leader (U := U) (W := W)) = Fintype.card U := by
  classical
  unfold Counting.leaderCount
  rw [Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_sum_type]
  simp [leader]

/-- The graph is an admissible static execution with precisely ell leaders. -/
theorem admissible (z : U) (z' : W) (c : Nat)
    (hc : c = 1 ∨ c = Fintype.card U) :
    Admissible (Fintype.card U) (network z z' c) leader where
  positive := left_card_pos z
  leaders := leader_count
  connected := fun _ _ ↦ stronglyConnected z z' c hc

omit [Fintype W] in
/-- Every arc multiplicity is bounded by the number of leaders. -/
theorem multiplicity_le_leaders (z : U) (z' : W) (c : Nat)
    (hc : c = 1 ∨ c = Fintype.card U) (u v : Sum U W) :
    edge z z' c u v ≤ Fintype.card U := by
  have hc_le : c ≤ Fintype.card U := by
    rcases hc with rfl | rfl
    · exact left_card_pos z
    · exact le_rfl
  have hdiv := Nat.div_le_self (Fintype.card U) c
  have hpos := left_card_pos z
  cases u <;> cases v <;> dsimp only [edge] <;> (try split_ifs) <;> omega

end Counting.TwoCenter
