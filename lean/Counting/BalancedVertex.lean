import Counting.Network
import Mathlib.Data.Finset.Max
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Logic.Equiv.Option

/-! Elimination of a balanced loopless vertex by pairing its incident arcs.
The pairing proof maximizes the finite number of reachable ordered pairs.
-/

namespace Counting.BalancedVertex
open DirectedCounting Relation

abbrev Reach {V : Type*} (r : V → V → Prop) := ReflTransGen r

/-- A path inside a strongly connected component can stop on its first arrival
at the target. Every remaining edge has both endpoints in that component. -/
theorem component_path {V : Type*} {r : V → V → Prop} {s t : V}
    (path : Reach r s t) (back : Reach r t s) :
    Reach (fun u v => r u v ∧ u ≠ t ∧ Reach r t u ∧ Reach r v t) s t := by
  classical
  induction path using ReflTransGen.head_induction_on with
  | refl => exact .refl
  | @head u v edge rest ih =>
      by_cases hu : u = t
      · subst u; exact .refl
      · exact ReflTransGen.head ⟨edge, hu, back, rest⟩ (ih (back.tail edge))

noncomputable def predecessors {V : Type*} [Fintype V] (r : V → V → Prop) (v : V) : Finset V := by
  classical
  exact Finset.univ.filter (fun u => Reach r u v)

noncomputable def successors {V : Type*} [Fintype V] (r : V → V → Prop) (v : V) : Finset V := by
  classical
  exact Finset.univ.filter (fun u => Reach r v u)

/-- Every finite relation has a source component. -/
theorem exists_source {V : Type*} [Fintype V] [Nonempty V] (r : V → V → Prop) :
    ∃ b, ∀ a, Reach r a b → Reach r b a := by
  classical
  obtain ⟨b, _, minimal⟩ := Finset.exists_min_image Finset.univ
    (fun v => (predecessors r v).card) Finset.univ_nonempty
  refine ⟨b, fun a hab => ?_⟩
  by_contra hba
  have sub : predecessors r a ⊆ predecessors r b := by
    intro v hv
    simp only [predecessors, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    exact hv.trans hab
  have ne : predecessors r a ≠ predecessors r b := by
    intro heq
    have hb : b ∈ predecessors r b := by simp [predecessors, ReflTransGen.refl]
    rw [← heq] at hb
    exact hba (by simpa [predecessors] using hb)
  have strict := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨sub, ne⟩)
  have lower := minimal a (Finset.mem_univ a)
  omega

/-- A non-strongly-connected finite relation has distinct source and sink
components, with no path from the chosen sink back to the chosen source. -/
theorem exists_source_sink {V : Type*} [Fintype V] [Nonempty V]
    (r : V → V → Prop) (notConnected : ¬ StronglyConnected r) :
    ∃ b c,
      (∀ a, Reach r a b → Reach r b a) ∧
      (∀ d, Reach r c d → Reach r d c) ∧ ¬ Reach r c b := by
  classical
  obtain ⟨b, source⟩ := exists_source r
  let outside := Finset.univ.filter (fun c => ¬ Reach r c b)
  have nonempty : outside.Nonempty := by
    by_contra hn
    have hall : ∀ c, Reach r c b := by
      intro c
      by_contra hc
      exact hn ⟨c, Finset.mem_filter.mpr ⟨Finset.mem_univ c, hc⟩⟩
    exact notConnected (fun x y => (hall x).trans (source y (hall y)))
  obtain ⟨c, hc, minimal⟩ := Finset.exists_min_image outside
    (fun v => (successors r v).card) nonempty
  have notcb : ¬ Reach r c b := (Finset.mem_filter.mp hc).2
  refine ⟨b, c, source, ?_, notcb⟩
  intro d hcd
  by_contra hdc
  have hd : d ∈ outside := Finset.mem_filter.mpr
    ⟨Finset.mem_univ d, fun hdb => notcb (hcd.trans hdb)⟩
  have sub : successors r d ⊆ successors r c := by
    intro v hv
    simp only [successors, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    exact hcd.trans hv
  have ne : successors r d ≠ successors r c := by
    intro heq
    have hc' : c ∈ successors r c := by simp [successors, ReflTransGen.refl]
    rw [← heq] at hc'
    exact hdc (by simpa [successors] using hc')
  have strict := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨sub, ne⟩)
  have lower := minimal d hd
  omega

variable {V I : Type*}

/-- One index labels each incoming arc and one outgoing arc at the hub. -/
def hub (base : V → V → Prop) (source target : I → V) : Option V → Option V → Prop
  | none, none => False
  | some x, none => ∃ i, source i = x
  | none, some y => ∃ i, target i = y
  | some x, some y => base x y

def shortcut (base : V → V → Prop) (source target : I → V)
    (pairing : Equiv.Perm I) (x y : V) : Prop :=
  base x y ∨ ∃ i, source i = x ∧ target (pairing i) = y

theorem hub_path_out (base : V → V → Prop) (source target : I → V)
    {b : V} (path : Reach (hub base source target) none (some b)) :
    ∃ i, Reach base (target i) b := by
  have aux : ∀ endpoint, Reach (hub base source target) none endpoint →
      match endpoint with | none => True | some v => ∃ i, Reach base (target i) v := by
    intro endpoint hp
    induction hp with
    | refl => trivial
    | @tail u v _ edge ih =>
      cases v with
      | none => trivial
      | some v =>
        cases u with
        | none => obtain ⟨i, rfl⟩ := edge; exact ⟨i, .refl⟩
        | some u => obtain ⟨i, hi⟩ := ih; exact ⟨i, hi.tail edge⟩
  exact aux _ path

theorem hub_path_in (base : V → V → Prop) (source target : I → V)
    {c : V} (path : Reach (hub base source target) (some c) none) :
    ∃ i, Reach base c (source i) := by
  have aux : ∀ start, Reach (hub base source target) start none →
      match start with | none => True | some v => ∃ i, Reach base v (source i) := by
    intro start hp
    induction hp using ReflTransGen.head_induction_on with
    | refl => trivial
    | @head u v edge _ ih =>
      cases u with
      | none => trivial
      | some u =>
        cases v with
        | none => obtain ⟨i, rfl⟩ := edge; exact ⟨i, .refl⟩
        | some v => obtain ⟨i, hi⟩ := ih; exact ⟨i, ReflTransGen.head edge hi⟩
  exact aux _ path

theorem base_reach_shortcut (base : V → V → Prop) (source target : I → V)
    (pairing : Equiv.Perm I) {a b : V} (path : Reach base a b) :
    Reach (shortcut base source target pairing) a b := by
  induction path with
  | refl => exact .refl
  | tail _ edge ih => exact ih.tail (Or.inl edge)

theorem reach_lift {r s : V → V → Prop}
    (lift : ∀ x y, r x y → Reach s x y) {a b : V} (path : Reach r a b) :
    Reach s a b := by
  induction path with
  | refl => exact .refl
  | tail _ edge ih => exact ih.trans (lift _ _ edge)

/-- In a disconnected pairing, the hub supplies two shortcuts lying in
different components, each with an internal return path. -/
theorem switch_indices [Fintype V] [Nonempty V]
    (base : V → V → Prop) (source target : I → V) (pairing : Equiv.Perm I)
    (connected : StronglyConnected (hub base source target))
    (disconnected : ¬ StronglyConnected (shortcut base source target pairing)) :
    ∃ i j,
      Reach (shortcut base source target pairing) (target (pairing i)) (source i) ∧
      Reach (shortcut base source target pairing) (target (pairing j)) (source j) ∧
      ¬ Reach (shortcut base source target pairing) (source j) (target (pairing i)) := by
  obtain ⟨b, c, sourceComponent, sinkComponent, notcb⟩ :=
    exists_source_sink _ disconnected
  obtain ⟨k, hkb⟩ := hub_path_out base source target (connected none (some b))
  obtain ⟨j, hcj⟩ := hub_path_in base source target (connected (some c) none)
  let i := pairing.symm k
  have hik : pairing i = k := pairing.apply_symm_apply k
  have e₁ : shortcut base source target pairing (source i) (target (pairing i)) :=
    Or.inr ⟨i, rfl, rfl⟩
  have e₂ : shortcut base source target pairing (source j) (target (pairing j)) :=
    Or.inr ⟨j, rfl, rfl⟩
  have hib : Reach (shortcut base source target pairing) (target (pairing i)) b := by
    rw [hik]
    exact base_reach_shortcut base source target pairing hkb
  have hcj' := base_reach_shortcut base source target pairing hcj
  refine ⟨i, j, hib.trans (sourceComponent _ (ReflTransGen.head e₁ hib)),
    (sinkComponent _ (hcj'.tail e₂)).trans hcj', ?_⟩
  exact fun h => notcb (hcj'.trans (h.trans hib))

/-- Swapping the partners of two shortcuts with the indicated internal
return paths preserves every old reachability and creates a new one. -/
theorem switch_improves [DecidableEq I]
    (base : V → V → Prop) (source target : I → V) (pairing : Equiv.Perm I)
    (i j : I)
    (back₁ : Reach (shortcut base source target pairing) (target (pairing i)) (source i))
    (back₂ : Reach (shortcut base source target pairing) (target (pairing j)) (source j))
    (separate : ¬ Reach (shortcut base source target pairing) (source j) (target (pairing i))) :
    (∀ x y, Reach (shortcut base source target pairing) x y →
      Reach (shortcut base source target ((Equiv.swap i j).trans pairing)) x y) ∧
    Reach (shortcut base source target ((Equiv.swap i j).trans pairing))
      (source j) (target (pairing i)) := by
  let r := shortcut base source target pairing
  let s := shortcut base source target ((Equiv.swap i j).trans pairing)
  have e₁ : r (source i) (target (pairing i)) := Or.inr ⟨i, rfl, rfl⟩
  have e₂ : r (source j) (target (pairing j)) := Or.inr ⟨j, rfl, rfl⟩
  have new₁ : s (source i) (target (pairing j)) := by
    exact Or.inr ⟨i, rfl, by simp⟩
  have new₂ : s (source j) (target (pairing i)) := by
    exact Or.inr ⟨j, rfl, by simp⟩
  have survives : ∀ u v, r u v → u ≠ source i → u ≠ source j → s u v := by
    intro u v edge hi hj
    rcases edge with hbase | ⟨k, hku, hkv⟩
    · exact Or.inl hbase
    · have hki : k ≠ i := by intro h; subst k; exact hi hku.symm
      have hkj : k ≠ j := by intro h; subst k; exact hj hku.symm
      exact Or.inr ⟨k, hku, by simpa [Equiv.swap_apply_of_ne_of_ne hki hkj] using hkv⟩
  have return₁ : Reach s (target (pairing i)) (source i) := by
    apply reach_lift (r := fun u v => r u v ∧ u ≠ source i ∧
      Reach r (source i) u ∧ Reach r v (source i)) _ (component_path back₁ (.single e₁))
    intro u v ⟨edge, hi, _, hv⟩
    apply ReflTransGen.single (survives u v edge hi ?_)
    intro h
    subst u
    exact separate ((ReflTransGen.head edge hv).tail e₁)
  have return₂ : Reach s (target (pairing j)) (source j) := by
    apply reach_lift (r := fun u v => r u v ∧ u ≠ source j ∧
      Reach r (source j) u ∧ Reach r v (source j)) _ (component_path back₂ (.single e₂))
    intro u v ⟨edge, hj, hu, _⟩
    apply ReflTransGen.single (survives u v edge ?_ hj)
    intro h
    subst u
    exact separate (hu.tail e₁)
  have replacement₁ : Reach s (source i) (target (pairing i)) :=
    (ReflTransGen.head new₁ return₂).tail new₂
  have replacement₂ : Reach s (source j) (target (pairing j)) :=
    (ReflTransGen.head new₂ return₁).tail new₁
  refine ⟨?_, .single new₂⟩
  intro x y path
  refine reach_lift (r := r) (s := s) ?_ path
  intro u v edge
  rcases edge with hbase | ⟨k, rfl, rfl⟩
  · exact .single (Or.inl hbase)
  · by_cases hi : k = i
    · subst k; exact replacement₁
    · by_cases hj : k = j
      · subst k; exact replacement₂
      · exact .single (Or.inr ⟨k, rfl, by simp [Equiv.swap_apply_of_ne_of_ne hi hj]⟩)

noncomputable def reachablePairs [Fintype V] (r : V → V → Prop) : Finset (V × V) := by
  classical
  exact Finset.univ.filter (fun xy => Reach r xy.1 xy.2)

/-- Pairing a finite balanced hub can preserve strong connectivity. -/
theorem exists_connected_pairing [Fintype V] [Nonempty V] [Fintype I]
    (base : V → V → Prop) (source target : I → V)
    (connected : StronglyConnected (hub base source target)) :
    ∃ pairing : Equiv.Perm I, StronglyConnected (shortcut base source target pairing) := by
  classical
  obtain ⟨pairing, _, maximal⟩ := Finset.exists_max_image Finset.univ
    (fun p : Equiv.Perm I => (reachablePairs (shortcut base source target p)).card)
    Finset.univ_nonempty
  refine ⟨pairing, ?_⟩
  by_contra disconnected
  obtain ⟨i, j, back₁, back₂, separate⟩ :=
    switch_indices base source target pairing connected disconnected
  obtain ⟨preserves, newPath⟩ := switch_improves base source target pairing i j back₁ back₂ separate
  let newPairing := (Equiv.swap i j).trans pairing
  have sub : reachablePairs (shortcut base source target pairing) ⊆
      reachablePairs (shortcut base source target newPairing) := by
    intro xy hxy
    simp only [reachablePairs, Finset.mem_filter, Finset.mem_univ, true_and] at hxy ⊢
    exact preserves _ _ hxy
  have ne : reachablePairs (shortcut base source target pairing) ≠
      reachablePairs (shortcut base source target newPairing) := by
    intro heq
    have hnew : (source j, target (pairing i)) ∈
        reachablePairs (shortcut base source target newPairing) := by
      simpa [reachablePairs, newPairing] using newPath
    rw [← heq] at hnew
    exact separate (by simpa [reachablePairs] using hnew)
  have strict := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨sub, ne⟩)
  have upper := maximal newPairing (Finset.mem_univ newPairing)
  omega

abbrev Incoming (D : Option V → Option V → Nat) := Σ v : V, Fin (D (some v) none)
abbrev Outgoing (D : Option V → Option V → Nat) := Σ v : V, Fin (D none (some v))

/-- Each incoming arc is paired bijectively with an outgoing arc. Multiplicity
counts the pairs with the requested endpoints; other arcs are retained. -/
noncomputable def eliminate [Fintype V] (D : Option V → Option V → Nat)
    (matching : Incoming D ≃ Outgoing D) (x y : V) : Nat := by
  classical
  exact D (some x) (some y) +
    (Finset.univ.filter (fun i : Incoming D => i.1 = x ∧ (matching i).1 = y)).card

theorem eliminate_positive_iff [Fintype V] (D : Option V → Option V → Nat)
    (matching : Incoming D ≃ Outgoing D) (x y : V) :
    0 < eliminate D matching x y ↔
      0 < D (some x) (some y) ∨ ∃ i : Incoming D, i.1 = x ∧ (matching i).1 = y := by
  classical
  simp [eliminate, Finset.card_pos, Finset.Nonempty]

/-- The balanced-vertex lemma in the natural-multiplicity model. The removed
vertex is `none`; at least one remaining vertex must exist. -/
theorem eliminate_balanced_vertex [Fintype V] [Nonempty V]
    (D : Option V → Option V → Nat)
    (loopless : D none none = 0)
    (balanced : ∑ v : V, D (some v) none = ∑ v : V, D none (some v))
    (connected : StronglyConnected (fun u v => 0 < D u v)) :
    ∃ matching : Incoming D ≃ Outgoing D,
      StronglyConnected (fun x y => 0 < eliminate D matching x y) := by
  classical
  have cards : Fintype.card (Incoming D) = Fintype.card (Outgoing D) := by
    simpa [Incoming, Outgoing, Fintype.card_sigma] using balanced
  let initial : Incoming D ≃ Outgoing D := Fintype.equivOfCardEq cards
  let source : Incoming D → V := Sigma.fst
  let target : Incoming D → V := fun i => (initial i).1
  let base : V → V → Prop := fun x y => 0 < D (some x) (some y)
  have hub_iff : ∀ u v, hub base source target u v ↔ 0 < D u v := by
    intro u v
    cases u with
    | none =>
      cases v with
      | none => simp [hub, loopless]
      | some y =>
        constructor
        · rintro ⟨i, hi⟩
          have h : 0 < D none (some (initial i).1) := Nat.zero_lt_of_lt (initial i).2.isLt
          change (initial i).1 = y at hi
          rw [hi] at h
          omega
        · intro hy
          let o : Outgoing D := ⟨y, ⟨0, hy⟩⟩
          exact ⟨initial.symm o, by simp [target, o]⟩
    | some x =>
      cases v with
      | none =>
        constructor
        · rintro ⟨i, hi⟩
          have h : 0 < D (some i.1) none := Nat.zero_lt_of_lt i.2.isLt
          change i.1 = x at hi
          rw [hi] at h
          omega
        · intro hx
          exact ⟨⟨x, ⟨0, hx⟩⟩, rfl⟩
      | some y => rfl
  have hubConnected : StronglyConnected (hub base source target) := by
    intro u v
    exact reach_lift (fun x y edge => .single ((hub_iff x y).mpr edge)) (connected u v)
  obtain ⟨pairing, hp⟩ := exists_connected_pairing base source target hubConnected
  refine ⟨pairing.trans initial, fun x y => ?_⟩
  apply reach_lift (r := shortcut base source target pairing) _ (hp x y)
  intro u v edge
  apply ReflTransGen.single
  rw [eliminate_positive_iff]
  exact edge

/-- Reindex an arbitrary distinguished vertex by `none`, keeping all other
vertices as their original values equipped with a proof of inequality. -/
def vertexGraph {T : Type*} (D : T → T → Nat) (z : T) :
    Option {v : T // v ≠ z} → Option {v : T // v ≠ z} → Nat
  | none, none => D z z
  | some x, none => D x z
  | none, some y => D z y
  | some x, some y => D x y

/-- The paper's balanced-vertex lemma, quantified over any finite carrier
and any loopless balanced vertex with at least one other vertex. -/
theorem eliminate_at_vertex {T : Type*} [Fintype T] [DecidableEq T]
    (D : T → T → Nat) (z : T)
    (other : ∃ v, v ≠ z) (loopless : D z z = 0)
    (balanced : ∑ v : T, D v z = ∑ v : T, D z v)
    (connected : StronglyConnected (fun u v => 0 < D u v)) :
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
  apply eliminate_balanced_vertex (vertexGraph D z) loopless balance
  intro u v
  simpa using mapped (e u) (e v) (connected (e u) (e v))

end Counting.BalancedVertex
