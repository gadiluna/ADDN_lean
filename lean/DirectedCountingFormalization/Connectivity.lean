import Mathlib.Data.Set.Basic

/-!
# Directed support connectivity

The matrix support is represented by a binary relation.  Strong connectivity
means reachability in both directions (equivalently, reachability from every
vertex to every other vertex).  The only graph fact needed by the ratio
argument is that every nonempty proper set has an outgoing support edge.
-/

namespace DirectedCounting

/-- Every ordered pair is joined by a finite, possibly empty directed walk. -/
def StronglyConnected {ι : Type*} (r : ι → ι → Prop) : Prop :=
  ∀ i j, Relation.ReflTransGen r i j

/-- A one-step-closed set is closed along every finite directed walk. -/
theorem mem_of_reachable_of_closed {ι : Type*} {r : ι → ι → Prop}
    {Q : Set ι} (hclosed : ∀ ⦃i j⦄, i ∈ Q → r i j → j ∈ Q)
    {i j : ι} (p : Relation.ReflTransGen r i j) (hi : i ∈ Q) : j ∈ Q := by
  induction p with
  | refl => exact hi
  | tail _ hij ih => exact hclosed ih hij

/-- A nonempty proper set in a strongly connected digraph has an outgoing edge. -/
theorem exists_edge_leaving {ι : Type*} {r : ι → ι → Prop}
    (hsc : StronglyConnected r) {Q : Set ι}
    (hQ : ∃ i, i ∈ Q) (hproper : ∃ j, j ∉ Q) :
    ∃ i j, i ∈ Q ∧ j ∉ Q ∧ r i j := by
  classical
  by_contra hex
  have hclosed : ∀ ⦃i j⦄, i ∈ Q → r i j → j ∈ Q := by
    intro i j hi hij
    by_contra hj
    exact hex ⟨i, j, hi, hj, hij⟩
  obtain ⟨i, hi⟩ := hQ
  obtain ⟨j, hj⟩ := hproper
  exact hj (mem_of_reachable_of_closed hclosed (hsc i j) hi)

/-- Strong connectivity of the positive support implies the outgoing-cut property. -/
theorem support_has_outgoing_cut
    {q : ℕ} {M : ℕ → ℕ → ℕ}
    (hsc : StronglyConnected (fun i j : Fin q ↦ 0 < M i j))
    {Q : Fin q → Prop} (hQ : ∃ i, Q i) (hproper : ∃ j, ¬ Q j) :
    ∃ i j, Q i ∧ ¬ Q j ∧ 0 < M i j :=
  exists_edge_leaving hsc hQ hproper

end DirectedCounting
