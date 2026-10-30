import Counting.RealizabilityConstructionEliminate

/-! The expanded physical graph in the sufficiency proof. It contains the
actual agents and one auxiliary vertex for each old selected history.
All additions use natural multiplicities, including zero and large labels.
-/

namespace Counting.RealizabilityConstruction
open DirectedCounting

structure RoundData (A U W : Type*) where
  old : A → Option U
  new : A → Option W
  parent : W → U
  degree : W → Nat
  red : U → W → Nat
  nested : ∀ a v, new a = some v → old a = some (parent v)

namespace RoundData
variable {A U W : Type*} [Fintype A] (d : RoundData A U W)

noncomputable def retainedSupply (a : A) (u : U) : Nat := by
  classical
  exact match d.new a with
    | none => 0
    | some v => if d.parent v = u then d.degree v else 0

def requiredReceipt (u : U) (a : A) : Nat :=
  match d.new a with
  | none => 0
  | some v => d.red u v

noncomputable def supply (u : U) : Nat := ∑ a : A, d.retainedSupply a u
noncomputable def demand (u : U) : Nat := ∑ a : A, d.requiredReceipt u a

noncomputable def outside : Finset A := by
  classical
  exact Finset.univ.filter (fun a => d.new a = none)

noncomputable def leaving (u : U) : Finset A := by
  classical
  exact d.outside.filter (fun a => d.old a = some u)

noncomputable def pick (s : Finset A) : Option A :=
  if h : s.Nonempty then some (Classical.choose h) else none

omit [Fintype A] in
theorem pick_eq_some_mem {s : Finset A} {a : A} (h : pick s = some a) : a ∈ s := by
  classical
  unfold pick at h
  split at h
  · cases h
    exact Classical.choose_spec _
  · contradiction

omit [Fintype A] in
theorem pick_none_iff (s : Finset A) : pick s = none ↔ ¬ s.Nonempty := by
  classical
  simp [pick]

omit [Fintype A] in
theorem pick_some_iff (s : Finset A) : (pick s).isSome = true ↔ s.Nonempty := by
  classical
  simp [pick]

noncomputable def center : Option A := pick d.outside
noncomputable def leaver (u : U) : Option A := pick (d.leaving u)

theorem center_is_outside {a : A} (h : d.center = some a) : d.new a = none := by
  exact (Finset.mem_filter.mp (pick_eq_some_mem h)).2

theorem leaver_properties (u : U) {a : A} (h : d.leaver u = some a) :
    d.new a = none ∧ d.old a = some u := by
  classical
  have hm := Finset.mem_filter.mp (pick_eq_some_mem h)
  exact ⟨(Finset.mem_filter.mp hm.1).2, hm.2⟩

theorem leaver_none_of_center_none (h : d.center = none) (u : U) : d.leaver u = none := by
  classical
  apply (pick_none_iff _).mpr
  intro hleaving
  apply (pick_none_iff _).mp h
  obtain ⟨a, ha⟩ := hleaving
  exact ⟨a, (Finset.mem_filter.mp ha).1⟩

noncomputable def extraIn (a : A) (u : U) : Nat := by
  classical
  exact if d.leaver u = some a then d.demand u + 1 else 0

noncomputable def extraOut (u : U) (a : A) : Nat := by
  classical
  exact if d.center = some a then
    if (d.leaver u).isSome then d.supply u + 1 else d.supply u - d.demand u
  else 0

noncomputable def outsideArc (a b : A) : Nat := by
  classical
  exact if d.new a = none ∧ d.new b = none ∧ a ≠ b ∧
    (d.center = some a ∨ d.center = some b) then 1 else 0

noncomputable def expanded : A ⊕ U → A ⊕ U → Nat
  | .inl a, .inl b => d.outsideArc a b
  | .inl a, .inr u => d.retainedSupply a u + d.extraIn a u
  | .inr u, .inl a => d.requiredReceipt u a + d.extraOut u a
  | .inr _, .inr _ => 0

theorem sum_at_pick [DecidableEq A] (o : Option A) (w : Nat) :
    (∑ a : A, if o = some a then w else 0) = if o.isSome then w else 0 := by
  classical
  cases o with
  | none => simp
  | some a => simp

theorem expanded_aux_in [Fintype U] (u : U) :
    (∑ x : A ⊕ U, d.expanded x (.inr u)) =
      d.supply u + if (d.leaver u).isSome then d.demand u + 1 else 0 := by
  classical
  rw [Fintype.sum_sum_type]
  simp only [expanded, Finset.sum_const_zero, Nat.add_zero, Finset.sum_add_distrib]
  rw [show (∑ a : A, d.extraIn a u) = if (d.leaver u).isSome then d.demand u + 1 else 0 from
    sum_at_pick (d.leaver u) (d.demand u + 1)]
  rfl

theorem expanded_aux_out [Fintype U] (u : U) :
    (∑ x : A ⊕ U, d.expanded (.inr u) x) =
      d.demand u + if d.center.isSome then
        if (d.leaver u).isSome then d.supply u + 1 else d.supply u - d.demand u
      else 0 := by
  classical
  rw [Fintype.sum_sum_type]
  simp only [expanded, Finset.sum_const_zero, Nat.add_zero, Finset.sum_add_distrib]
  rw [show (∑ a : A, d.extraOut u a) = if d.center.isSome then
      if (d.leaver u).isSome then d.supply u + 1 else d.supply u - d.demand u else 0 from
    sum_at_pick d.center _]
  rfl

/-- Exactly the two balance cases of the compact count certificate. -/
structure Balanced : Prop where
  full : d.center = none → ∀ u, d.supply u = d.demand u
  proper : d.center ≠ none → ∀ u, d.leaver u = none → d.demand u ≤ d.supply u

theorem expanded_balanced [Fintype U] (balance : d.Balanced) (u : U) :
    (∑ x : A ⊕ U, d.expanded x (.inr u)) =
      ∑ x : A ⊕ U, d.expanded (.inr u) x := by
  rw [d.expanded_aux_in, d.expanded_aux_out]
  cases hc : d.center with
  | none => simp [d.leaver_none_of_center_none hc u, balance.full hc u]
  | some a =>
    cases hl : d.leaver u with
    | none =>
      have h := balance.proper (by simp [hc]) u hl
      simp only [Option.isSome_none, Option.isSome_some, Bool.false_eq_true,
        ↓reduceIte, Nat.add_zero]
      omega
    | some b => simp [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

theorem expanded_aux_loopless (u v : U) : d.expanded (.inr u) (.inr v) = 0 := rfl

theorem expanded_tails_typed (a : A) (u : U) (positive : 0 < d.expanded (.inl a) (.inr u)) :
    d.old a = some u := by
  classical
  change 0 < d.retainedSupply a u + d.extraIn a u at positive
  cases hn : d.new a with
  | none =>
    simp only [retainedSupply, hn, extraIn, Nat.zero_add] at positive
    split at positive
    · exact (d.leaver_properties u ‹_›).2
    · omega
  | some v =>
    have extra : d.extraIn a u = 0 := by
      unfold extraIn
      split
      · have h := (d.leaver_properties u ‹_›).1
        simp [hn] at h
      · rfl
    simp only [retainedSupply, hn, extra, Nat.add_zero] at positive
    split at positive
    · simpa only [‹d.parent v = u›] using d.nested a v hn
    · omega

theorem expanded_selected_receipt (u : U) (a : A) (v : W) (selected : d.new a = some v) :
    d.expanded (.inr u) (.inl a) = d.red u v := by
  classical
  have extra : d.extraOut u a = 0 := by
    unfold extraOut
    split
    · have h := d.center_is_outside ‹_›
      simp [selected] at h
    · rfl
  simp [expanded, requiredReceipt, selected, extra]

theorem expanded_selected_outdegree [Fintype U] (a : A) (v : W) (selected : d.new a = some v) :
    (∑ x : A ⊕ U, d.expanded (.inl a) x) = d.degree v := by
  classical
  have extra (u : U) : d.extraIn a u = 0 := by
    unfold extraIn
    split
    · have h := (d.leaver_properties u ‹_›).1
      simp [selected] at h
    · rfl
  rw [Fintype.sum_sum_type]
  simp [expanded, outsideArc, retainedSupply, selected, extra, eq_comm]

end RoundData
end Counting.RealizabilityConstruction
