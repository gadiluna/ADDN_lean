import Counting.BalancedVertexCounts

/-! The current paper's balanced-auxiliary-vertex lemma assumes reachability
only between the vertices that remain. The auxiliary vertex may be isolated.
Paths between remaining vertices are allowed to pass through the auxiliary.
-/

namespace Counting.BalancedVertex
open DirectedCounting Relation

variable {V : Type*}

/-- With no arc entering the auxiliary vertex, a path starting at a remaining
vertex stays in the induced graph on the remaining vertices. -/
theorem remaining_path_of_no_incoming (D : Option V → Option V → Nat)
    (noIncoming : ∀ v, D (some v) none = 0) (x y : V)
    (path : Reach (fun u v => 0 < D u v) (some x) (some y)) :
    Reach (fun u v => 0 < D (some u) (some v)) x y := by
  have stays : ∀ endpoint, Reach (fun u v => 0 < D u v) (some x) endpoint →
      ∃ v, endpoint = some v ∧
        Reach (fun u v => 0 < D (some u) (some v)) x v := by
    intro endpoint hp
    induction hp with
    | refl => exact ⟨x, rfl, .refl⟩
    | @tail u v _ edge ih =>
      obtain ⟨a, rfl, before⟩ := ih
      cases v with
      | none => simp [noIncoming] at edge
      | some b => exact ⟨b, rfl, before.tail edge⟩
  obtain ⟨v, hv, hp⟩ := stays (some y) path
  cases Option.some.inj hv
  exact hp

/-- If the auxiliary has an entering and a leaving arc, mutual reachability
of the remaining vertices already gives whole-graph strong connectivity. -/
theorem connected_of_remaining_reachable (D : Option V → Option V → Nat)
    (remaining : ∀ x y : V,
      Reach (fun u v => 0 < D u v) (some x) (some y))
    (incoming : ∃ x, 0 < D (some x) none)
    (outgoing : ∃ y, 0 < D none (some y)) :
    StronglyConnected (fun u v => 0 < D u v) := by
  obtain ⟨a, ha⟩ := incoming
  obtain ⟨b, hb⟩ := outgoing
  intro x y
  cases x with
  | none =>
    cases y with
    | none => exact .refl
    | some y => exact ReflTransGen.head hb (remaining b y)
  | some x =>
    cases y with
    | none => exact (remaining x a).tail ha
    | some y => exact remaining x y

/-- Balanced auxiliary elimination under exactly the current connectivity
hypothesis: only the remaining vertices must be mutually reachable in the
original graph. An isolated auxiliary is permitted. Each parallel arc is
paired individually, and loops at remaining vertices are allowed. -/
theorem eliminate_balanced_vertex_of_remaining_reachable [Fintype V] [Nonempty V]
    (D : Option V → Option V → Nat)
    (loopless : D none none = 0)
    (balanced : ∑ v : V, D (some v) none = ∑ v : V, D none (some v))
    (remaining : ∀ x y : V,
      Reach (fun u v => 0 < D u v) (some x) (some y)) :
    ∃ matching : Incoming D ≃ Outgoing D,
      StronglyConnected (fun x y => 0 < eliminate D matching x y) := by
  classical
  by_cases incoming : ∃ x, 0 < D (some x) none
  · have positive : 0 < ∑ v : V, D none (some v) := by
      rw [← balanced]
      obtain ⟨x, hx⟩ := incoming
      exact Finset.sum_pos_iff.mpr ⟨x, Finset.mem_univ x, hx⟩
    obtain ⟨y, _, hy⟩ := Finset.sum_pos_iff.mp positive
    exact eliminate_balanced_vertex D loopless balanced
      (connected_of_remaining_reachable D remaining incoming ⟨y, hy⟩)
  · have noIncoming : ∀ v, D (some v) none = 0 := by
      intro v
      exact Nat.eq_zero_of_not_pos (fun hv => incoming ⟨v, hv⟩)
    have cards : Fintype.card (Incoming D) = Fintype.card (Outgoing D) := by
      simpa [Incoming, Outgoing, Fintype.card_sigma] using balanced
    let matching : Incoming D ≃ Outgoing D := Fintype.equivOfCardEq cards
    refine ⟨matching, fun x y => ?_⟩
    apply reach_lift (r := fun u v => 0 < D (some u) (some v)) ?_
      (remaining_path_of_no_incoming D noIncoming x y (remaining x y))
    intro u v edge
    exact .single ((eliminate_positive_iff D matching u v).mpr (Or.inl edge))

/-- The manuscript statement on an arbitrary finite carrier and a designated
loopless balanced auxiliary vertex. No reachability to or from that vertex
is assumed; the path hypothesis refers only to pairs of other vertices. -/
theorem eliminate_at_vertex_of_remaining_reachable {T : Type*}
    [Fintype T] [DecidableEq T] (D : T → T → Nat) (z : T)
    (other : ∃ v, v ≠ z) (loopless : D z z = 0)
    (balanced : ∑ v : T, D v z = ∑ v : T, D z v)
    (remaining : ∀ x y, x ≠ z → y ≠ z → Reach (fun u v => 0 < D u v) x y) :
    ∃ matching : Incoming (vertexGraph D z) ≃ Outgoing (vertexGraph D z),
      StronglyConnected (fun x y => 0 < eliminate (vertexGraph D z) matching x y) := by
  classical
  letI : Nonempty {v : T // v ≠ z} := by
    obtain ⟨v, hv⟩ := other
    exact ⟨⟨v, hv⟩⟩
  have balance : ∑ v : {v : T // v ≠ z}, D v z =
      ∑ v : {v : T // v ≠ z}, D z v := by
    rw [Fintype.sum_eq_add_sum_subtype_ne (fun v => D v z) z,
      Fintype.sum_eq_add_sum_subtype_ne (fun v => D z v) z] at balanced
    exact Nat.add_left_cancel balanced
  let e := Equiv.optionSubtypeNe z
  have graph_eq : ∀ u v, vertexGraph D z u v = D (e u) (e v) := by
    intro u v
    cases u <;> cases v <;> rfl
  have mapped : ∀ a b, Reach (fun u v => 0 < D u v) a b →
      Reach (fun u v => 0 < vertexGraph D z u v) (e.symm a) (e.symm b) := by
    intro a b path
    induction path with
    | refl => exact .refl
    | @tail u v _ edge ih =>
      apply ih.tail
      simpa [graph_eq] using edge
  apply eliminate_balanced_vertex_of_remaining_reachable (vertexGraph D z) loopless balance
  intro x y
  have path : Reach (fun u v => 0 < D u v) (e (some x)) (e (some y)) :=
    remaining x.val y.val x.property y.property
  simpa using mapped (e (some x)) (e (some y)) path

end Counting.BalancedVertex
