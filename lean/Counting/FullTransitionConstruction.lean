import Counting.FullTransitionSpec

/-! Realize a balanced transition by introducing one auxiliary vertex per
occupied old class, and then eliminating these independent balanced vertices. -/

namespace Counting.FullTransition.Data
open DirectedCounting Relation RealizabilityConstruction

variable {A U W : Type*} [Fintype A] [Fintype U] [DecidableEq U]

abbrev Aux (d : Data U W) (tag : A → W) :=
  {u : U // ∃ a, d.parent (tag a) = u}

noncomputable instance auxFintype (d : Data U W) (tag : A → W) : Fintype (d.Aux tag) := by
  classical
  exact inferInstanceAs (Fintype {u : U // ∃ a, d.parent (tag a) = u})

def hub (d : Data U W) (tag : A → W) (a : A) : d.Aux tag :=
  ⟨d.parent (tag a), a, rfl⟩

def expanded (d : Data U W) (tag : A → W) : (A ⊕ d.Aux tag) → (A ⊕ d.Aux tag) → Nat
  | .inl a, .inr u => if d.parent (tag a) = u.val then d.degree (tag a) else 0
  | .inr u, .inl b => d.red u.val (tag b)
  | _, _ => 0

variable (d : Data U W) {tag : A → W}

omit [Fintype U] in
theorem red_zero_of_unoccupied (flow : d.Flow tag) {u : U}
    (empty : ¬ ∃ a, d.parent (tag a) = u) (b : A) : d.red u (tag b) = 0 := by
  have absent : ∀ a, d.parent (tag a) ≠ u := by simpa using empty
  have zero : (∑ a, d.red u (tag a)) = 0 := by simpa [absent] using (flow u).symm
  exact Finset.sum_eq_zero_iff.mp zero b (Finset.mem_univ b)

theorem expanded_outdegree (a : A) :
    (∑ q, d.expanded tag (.inl a) q) = d.degree (tag a) := by
  classical
  rw [Fintype.sum_sum_type]
  simp only [expanded, Finset.sum_const_zero, Nat.zero_add]
  rw [Finset.sum_eq_single (d.hub tag a)]
  · simp [hub]
  · intro u _ different
    have hn : d.parent (tag a) ≠ u.val := by
      intro eq
      exact different (Subtype.ext eq.symm)
    simp [hn]
  · simp

theorem expanded_receipts (flow : d.Flow tag) (b : A) (u : U) :
    (∑ z : d.Aux tag, if z.val = u then d.expanded tag (.inr z) (.inl b) else 0) =
      d.red u (tag b) := by
  classical
  by_cases occupied : ∃ a, d.parent (tag a) = u
  · rw [Finset.sum_eq_single (⟨u, occupied⟩ : d.Aux tag)]
    · simp [expanded]
    · intro z _ different
      have hn : z.val ≠ u := fun eq => different (Subtype.ext eq)
      simp [hn]
    · simp
  · have hn : ∀ z : d.Aux tag, z.val ≠ u := by
      intro z eq
      exact occupied (eq ▸ z.property)
    simp [hn, d.red_zero_of_unoccupied flow occupied b]

omit [Fintype U] in
theorem aux_successor (flow : d.Flow tag) (positive : ∀ v, 0 < d.degree v)
    (u : d.Aux tag) : ∃ b, 0 < d.red u.val (tag b) := by
  obtain ⟨a, ha⟩ := u.property
  have supply : 0 < ∑ x, if d.parent (tag x) = u.val then d.degree (tag x) else 0 :=
    Finset.sum_pos_iff.mpr ⟨a, Finset.mem_univ a, by simpa [ha] using positive (tag a)⟩
  rw [flow u.val] at supply
  obtain ⟨b, _, hb⟩ := Finset.sum_pos_iff.mp supply
  exact ⟨b, hb⟩

omit [Fintype U] in
theorem nonempty_node_path (flow : d.Flow tag) (represented : Function.Surjective tag)
    (positive : ∀ v, 0 < d.degree v) (connected : StronglyConnected d.Arc) (v w : W) :
    TransGen d.Arc v w := by
  obtain ⟨a, rfl⟩ := represented v
  obtain ⟨b, hb⟩ := d.aux_successor flow positive (d.hub tag a)
  exact (TransGen.single ⟨positive (tag a), hb⟩).trans_left (connected (tag b) w)

omit [Fintype A] [Fintype U] in
theorem expanded_lift_edge {a b : A} (edge : d.Arc (tag a) (tag b)) :
    ReflTransGen (fun x y => 0 < d.expanded tag x y) (.inl a) (.inl b) := by
  exact (ReflTransGen.single (b := .inr (d.hub tag a)) (by simpa [expanded, hub] using edge.1)).tail
    (by simpa [expanded, hub] using edge.2)

omit [Fintype U] in
theorem expanded_connected (flow : d.Flow tag) (represented : Function.Surjective tag)
    (positive : ∀ v, 0 < d.degree v) (connected : StronglyConnected d.Arc) :
    StronglyConnected (fun x y => 0 < d.expanded tag x y) := by
  have lift : ∀ v w, TransGen d.Arc v w → ∀ a b, tag a = v → tag b = w →
      ReflTransGen (fun x y => 0 < d.expanded tag x y) (.inl a) (.inl b) := by
    intro v w path
    induction path with
    | single edge =>
      intro a b ha hb
      exact d.expanded_lift_edge (by simpa [ha, hb] using edge)
    | @tail v w path edge ih =>
      intro a b ha hb
      obtain ⟨c, hc⟩ := represented v
      exact (ih a c ha hc).trans (d.expanded_lift_edge (by simpa [hc, hb] using edge))
  have physical (a b : A) :
      ReflTransGen (fun x y => 0 < d.expanded tag x y) (.inl a) (.inl b) :=
    lift _ _ (d.nonempty_node_path flow represented positive connected (tag a) (tag b)) a b rfl rfl
  have entering (u : d.Aux tag) : ∃ a, 0 < d.expanded tag (.inl a) (.inr u) := by
    obtain ⟨a, ha⟩ := u.property
    exact ⟨a, by simpa [expanded, ha] using positive (tag a)⟩
  have leaving (u : d.Aux tag) : ∃ b, 0 < d.expanded tag (.inr u) (.inl b) :=
    d.aux_successor flow positive u
  intro x y
  cases x with
  | inl a =>
    cases y with
    | inl b => exact physical a b
    | inr u =>
      obtain ⟨b, hb⟩ := entering u
      exact (physical a b).tail hb
  | inr u =>
    obtain ⟨a, ha⟩ := leaving u
    cases y with
    | inl b => exact (physical a b).head ha
    | inr v =>
      obtain ⟨b, hb⟩ := entering v
      have start : ReflTransGen (fun x y => 0 < d.expanded tag x y) (.inr u) (.inl b) :=
        (physical a b).head ha
      exact start.tail hb

/-- The balanced auxiliary construction realizes the prescribed physical
degrees and individual receipts from every old class. -/
theorem sufficient [Nonempty A] (flow : d.Flow tag) (represented : Function.Surjective tag)
    (conditions : d.Conditions) : ∃ E, d.Realizes tag E := by
  classical
  obtain ⟨E, hE⟩ := eliminate_many_colored (d.expanded tag) (fun a => d.parent (tag a))
    Subtype.val (fun _ _ => rfl) (fun u => flow u.val)
    (d.expanded_connected flow represented conditions.1 conditions.2.2)
    (by intro a u edge; by_contra hn; simp [expanded, hn] at edge)
  refine ⟨E, hE.connected, ?_, ?_⟩
  · intro a
    exact (hE.outdegree a).trans (d.expanded_outdegree a)
  · intro u b
    simpa [expanded] using (hE.colored b u).trans
      (by simpa [expanded] using d.expanded_receipts flow b u)

end Counting.FullTransition.Data
