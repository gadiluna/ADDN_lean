import Counting.RealizabilityConstructionGraph

namespace Counting.RealizabilityConstruction
open DirectedCounting Relation

/-- A nontrivial strongly connected type graph lifts when every type is
represented and every type edge can be followed between arbitrary
representatives. The nontriviality premise handles distinct agents of
the same type without assuming an internal edge between those agents. -/
theorem connected_of_representatives {A Q : Type*} [Nontrivial Q]
    (physical : A → A → Prop) (types : Q → Q → Prop) (rep : A → Q → Prop)
    (covered : ∀ a, ∃ q, rep a q) (inhabited : ∀ q, ∃ a, rep a q)
    (liftEdge : ∀ p q, types p q → ∀ a b, rep a p → rep b q → ReflTransGen physical a b)
    (connected : StronglyConnected types) : StronglyConnected physical := by
  have liftPath : ∀ p q, TransGen types p q →
      ∀ a b, rep a p → rep b q → ReflTransGen physical a b := by
    intro p q path
    induction path with
    | single edge => exact liftEdge _ _ edge
    | @tail q r path edge ih =>
      intro a b ha hb
      obtain ⟨c, hc⟩ := inhabited q
      exact (ih a c ha hc).trans (liftEdge q r edge c b hc hb)
  have strict (p q : Q) (different : p ≠ q) : TransGen types p q := by
    obtain eq | path := reflTransGen_iff_eq_or_transGen.mp (connected p q)
    · exact False.elim (different eq.symm)
    · exact path
  intro a b
  obtain ⟨p, ha⟩ := covered a
  obtain ⟨q, hb⟩ := covered b
  by_cases eq : p = q
  · obtain ⟨r, hr⟩ := exists_ne p
    obtain ⟨c, hc⟩ := inhabited r
    exact (liftPath p r (strict p r hr.symm) a c ha hc).trans
      (liftPath r q (strict r q (by simpa [← eq] using hr)) c b hc hb)
  · exact liftPath p q (strict p q eq) a b ha hb

namespace RoundData
variable {A U W : Type*} [Fintype A] (d : RoundData A U W)

abbrev OutsideVertex := {_z : Unit // d.center.isSome = true}
abbrev TypeVertex := W ⊕ (U ⊕ d.OutsideVertex)

def typeArc : d.TypeVertex → d.TypeVertex → Prop
  | .inl v, .inr (.inl u) => d.parent v = u ∧ 0 < d.degree v
  | .inr (.inl u), .inl v => 0 < d.red u v
  | .inr (.inr _), .inr (.inl u) => (d.leaver u).isSome = true
  | .inr (.inl u), .inr (.inr _) =>
      (d.leaver u).isSome = true ∨ d.demand u < d.supply u
  | _, _ => False

def represents : A ⊕ U → d.TypeVertex → Prop
  | .inl a, .inl v => d.new a = some v
  | .inl a, .inr (.inr _) => d.new a = none
  | .inr u, .inr (.inl v) => u = v
  | _, _ => False

theorem center_exists_of_outside (a : A) (outside : d.new a = none) :
    d.center.isSome = true := by
  classical
  apply (pick_some_iff _).mpr
  exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, outside⟩⟩

theorem physical_represented (x : A ⊕ U) : ∃ q, d.represents x q := by
  cases x with
  | inr u => exact ⟨.inr (.inl u), rfl⟩
  | inl a =>
    cases hn : d.new a with
    | some v => exact ⟨.inl v, hn⟩
    | none => exact ⟨.inr (.inr ⟨(), d.center_exists_of_outside a hn⟩), hn⟩

theorem type_represented (newNonempty : ∀ v, ∃ a, d.new a = some v) (q : d.TypeVertex) :
    ∃ x, d.represents x q := by
  rcases q with v | u | j
  · obtain ⟨a, ha⟩ := newNonempty v
    exact ⟨.inl a, ha⟩
  · exact ⟨.inr u, rfl⟩
  · have hj := j.property
    cases hc : d.center with
    | none => simp [hc] at hj
    | some a => exact ⟨.inl a, d.center_is_outside hc⟩

theorem outside_reachable (a b : A) (ha : d.new a = none) (hb : d.new b = none) :
    ReflTransGen (fun x y => 0 < d.expanded x y) (.inl a) (.inl b) := by
  classical
  have existsCenter := d.center_exists_of_outside a ha
  cases hc : d.center with
  | none => simp [hc] at existsCenter
  | some c =>
    have hout := d.center_is_outside hc
    have first : ReflTransGen (fun x y => 0 < d.expanded x y) (.inl a) (.inl c) := by
      by_cases eq : a = c
      · subst a; exact .refl
      · exact .single (by simp [expanded, outsideArc, ha, hout, eq, hc])
    have last : ReflTransGen (fun x y => 0 < d.expanded x y) (.inl c) (.inl b) := by
      by_cases eq : c = b
      · subst b; exact .refl
      · exact .single (by simp [expanded, outsideArc, hb, hout, eq, hc])
    exact first.trans last

theorem type_edge_lifts (p q : d.TypeVertex) (edge : d.typeArc p q)
    (x y : A ⊕ U) (hx : d.represents x p) (hy : d.represents y q) :
    ReflTransGen (fun a b => 0 < d.expanded a b) x y := by
  classical
  rcases p with v | u | j <;> rcases q with w | z | i
  all_goals simp only [typeArc] at edge
  · rcases x with a | a <;> rcases y with b | b
    all_goals simp only [represents] at hx hy
    subst b
    exact .single (by
      have h : d.retainedSupply a z = d.degree v := by simp [retainedSupply, hx, edge.1]
      change 0 < d.retainedSupply a z + d.extraIn a z
      rw [h]
      omega)
  · rcases x with a | a <;> rcases y with b | b
    all_goals simp only [represents] at hx hy
    subst a
    exact .single (by rw [d.expanded_selected_receipt u b w hy]; exact edge)
  · rcases x with a | a <;> rcases y with b | b
    all_goals simp only [represents] at hx hy
    subst a
    have hj := i.property
    cases hc : d.center with
    | none => simp [hc] at hj
    | some c =>
      have first : 0 < d.expanded (.inr u) (.inl c) := by
        change 0 < d.requiredReceipt u c + d.extraOut u c
        simp only [extraOut, hc, if_true]
        rcases edge with hl | more
        · simp only [hl, if_true]; omega
        · cases hl : d.leaver u with
          | none => simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte]; omega
          | some e => simp only [Option.isSome_some, ↓reduceIte]; omega
      exact ReflTransGen.head first (d.outside_reachable c b (d.center_is_outside hc) hy)
  · rcases x with a | a <;> rcases y with b | b
    all_goals simp only [represents] at hx hy
    subst b
    cases hl : d.leaver z with
    | none => simp [hl] at edge
    | some c =>
      have hc := (d.leaver_properties z hl).1
      have last : 0 < d.expanded (.inl c) (.inr z) := by
        simp [expanded, extraIn, hl]
      exact (d.outside_reachable a c hx hc).tail last

/-- Expanding each new type into its selected agents, joining all outside
agents through one center, and adding the prescribed balancing arcs
preserves strong connectivity of the certificate graph. -/
theorem expanded_connected [Nonempty W] [Nonempty U]
    (newNonempty : ∀ v, ∃ a, d.new a = some v)
    (connected : StronglyConnected d.typeArc) :
    StronglyConnected (fun x y => 0 < d.expanded x y) := by
  letI : Nontrivial d.TypeVertex := ⟨⟨.inl (Classical.choice inferInstance),
    .inr (.inl (Classical.choice inferInstance)), Sum.inl_ne_inr⟩⟩
  exact connected_of_representatives _ _ d.represents d.physical_represented
    (d.type_represented newNonempty) d.type_edge_lifts connected

end RoundData
end Counting.RealizabilityConstruction
