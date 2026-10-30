import Counting.TailExposure

/-!
# Causal-support upper bound from the actual visible labels

The support is a set of physical agents. Each backward step retains every
selected target and adds its incoming neighbors. Incoming multiplicities
are summed over the visible previous history classes, without assuming
that an entire visible fiber belongs to the support.
-/

namespace Counting.SupportBound

open DirectedCounting PaperHistory
open scoped BigOperators

/-- The number of distinct incoming neighbors is at most the incoming arc count. -/
theorem predecessor_card_le_inDegree {V : Type} [Fintype V]
    (edge : V → V → Nat) (target : V) :
    (Finset.univ.filter (fun source ↦ 0 < edge source target)).card ≤
      ∑ source, edge source target := by
  classical
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  apply Finset.sum_le_sum
  intro source _
  split_ifs <;> omega

/-- One backward step grows any selected set by at most the factor `1+D`
when every selected target receives at most `D` arcs, counting multiplicity. -/
theorem backward_card_le {V : Type} [Fintype V] [DecidableEq V]
    (edge : V → V → Nat) (selected : Finset V) (D : Nat)
    (degreeBound : ∀ target ∈ selected, (∑ source, edge source target) ≤ D) :
    (selected.biUnion (fun target ↦
      insert target (Finset.univ.filter (fun source ↦ 0 < edge source target)))).card ≤
        (1 + D) * selected.card := by
  have bound := Finset.card_biUnion_le_card_mul selected
    (fun target ↦ insert target (Finset.univ.filter (fun source ↦ 0 < edge source target)))
    (1 + D) (by
      intro target ht
      exact (Finset.card_insert_le _ _).trans (by
        have hpred := predecessor_card_le_inDegree edge target
        have hdegree := degreeBound target ht
        omega))
  simpa [Nat.mul_comm] using bound

/-- The generic backward growth estimate instantiated on actual causal support. -/
theorem causalSupport_step_card_le {V : Type} [Fintype V]
    (G : Nat → V → V → Nat) (r d : Nat) (observer : V) (D : Nat)
    (degreeBound : ∀ target ∈ causalSupport G (r + 1) d observer,
      (∑ source, G (r + 1) source target) ≤ D) :
    (causalSupport G r (d + 1) observer).card ≤
      (1 + D) * (causalSupport G (r + 1) d observer).card := by
  classical
  have heq : causalSupport G r (d + 1) observer =
      (causalSupport G (r + 1) d observer).biUnion (fun target ↦
        insert target (Finset.univ.filter (fun source ↦ 0 < G (r + 1) source target))) := by
    ext source
    simp only [mem_causalSupport_succ, Finset.mem_biUnion, Finset.mem_insert,
      Finset.mem_filter, Finset.mem_univ, true_and]
    aesop
  rw [heq]
  exact backward_card_le _ _ D degreeBound

/-- Iterating the physical incoming-degree bound yields the exponential
support bound. Only targets inside the appropriate causal support are bounded. -/
theorem causalSupport_card_le_pow {V : Type} [Fintype V]
    (G : Nat → V → V → Nat) (r d : Nat) (observer : V) (D : Nat)
    (degreeBound : ∀ k e, r < k → k + e = r + d →
      ∀ target ∈ causalSupport G k e observer,
        (∑ source, G k source target) ≤ D) :
    (causalSupport G r d observer).card ≤ (1 + D) ^ d := by
  induction d generalizing r with
  | zero => simp
  | succ d ih =>
      have hstep := causalSupport_step_card_le G r d observer D
        (degreeBound (r + 1) d (by omega) (by omega))
      have hnext := ih (r + 1) (by
        intro k e hk heq
        exact degreeBound k e (by omega) (by omega))
      exact hstep.trans (by
        simpa [pow_succ, Nat.mul_comm] using Nat.mul_le_mul_left (1 + D) hnext)

/-- Every positive incoming arc to the next support has a visible old source class. -/
theorem incoming_source_visible {V : Type} [Fintype V]
    (G : Nat → V → V → Nat) (leader : V → Bool) (r d : Nat)
    (observer source target : V)
    (selected : target ∈ causalSupport G (r + 1) d observer)
    (arc : 0 < G (r + 1) source target) :
    classOf G leader r source ∈ visibleNodes G leader r (d + 1) observer := by
  classical
  apply Finset.mem_image.mpr
  exact ⟨source, (mem_causalSupport_succ G r d observer source).mpr
    (Or.inr ⟨target, selected, arc⟩), rfl⟩

/-- Incoming arcs are exactly the sum of red multiplicities over visible old nodes. -/
theorem inDegree_eq_visible_red_sum {V : Type} [Fintype V]
    (G : Nat → V → V → Nat) (leader : V → Bool) (r d : Nat)
    (observer target : V) (selected : target ∈ causalSupport G (r + 1) d observer) :
    (∑ source, G (r + 1) source target) =
      ∑ node ∈ visibleNodes G leader r (d + 1) observer,
        redMultiplicity G leader r node (classOf G leader (r + 1) target) := by
  classical
  symm
  calc
    _ = ∑ node ∈ visibleNodes G leader r (d + 1) observer,
        ∑ source ∈ fiber G leader r node, G (r + 1) source target := by
      apply Finset.sum_congr rfl
      intro node _
      exact (incoming_eq_redMultiplicity G leader r node
        (classOf G leader (r + 1) target) (by simp)).symm
    _ = ∑ source ∈ Finset.univ.filter
        (fun source ↦ classOf G leader r source ∈ visibleNodes G leader r (d + 1) observer),
        G (r + 1) source target := by
      exact Finset.sum_fiberwise_eq_sum_filter Finset.univ _ (classOf G leader r) _
    _ = _ := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro source _ hnot
      by_contra hnonzero
      have hvisible := incoming_source_visible G leader r d observer source target
        selected (Nat.pos_of_ne_zero hnonzero)
      exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvisible⟩)

/-- At most `nu` visible old nodes and red multiplicity at most `M` imply
incoming degree at most `nu*M` for every target in the next causal support. -/
theorem inDegree_le_visible_bounds {V : Type} [Fintype V]
    (G : Nat → V → V → Nat) (leader : V → Bool) (r d : Nat)
    (observer target : V) (nu M : Nat)
    (selected : target ∈ causalSupport G (r + 1) d observer)
    (nodes : (visibleNodes G leader r (d + 1) observer).card ≤ nu)
    (labels : ∀ old ∈ visibleNodes G leader r (d + 1) observer,
      ∀ new ∈ visibleNodes G leader (r + 1) d observer,
        redMultiplicity G leader r old new ≤ M) :
    (∑ source, G (r + 1) source target) ≤ nu * M := by
  classical
  rw [inDegree_eq_visible_red_sum G leader r d observer target selected]
  have hnew : classOf G leader (r + 1) target ∈
      visibleNodes G leader (r + 1) d observer := Finset.mem_image.mpr ⟨target, selected, rfl⟩
  calc
    _ ≤ ∑ _node ∈ visibleNodes G leader r (d + 1) observer, M :=
      Finset.sum_le_sum (fun old hold ↦ labels old hold _ hnew)
    _ = (visibleNodes G leader r (d + 1) observer).card * M := by simp
    _ ≤ nu * M := Nat.mul_le_mul_right M nodes

/-- The paper's `K=(1+nu*M)^t` bound for the initial causal support of an
actual depth-`t` vista. Here `nu` bounds every visible level's node count and
`M` bounds each visible red label; a bound on the whole vista suffices. -/
theorem initial_support_card_le_pow {V : Type} [Fintype V]
    (G : Nat → V → V → Nat) (leader : V → Bool) (t : Nat)
    (observer : V) (nu M : Nat)
    (nodes : ∀ r, r < t → (visibleNodes G leader r (t - r) observer).card ≤ nu)
    (labels : ∀ r, r < t → ∀ old ∈ visibleNodes G leader r (t - r) observer,
      ∀ new ∈ visibleNodes G leader (r + 1) (t - (r + 1)) observer,
        redMultiplicity G leader r old new ≤ M) :
    (causalSupport G 0 t observer).card ≤ (1 + nu * M) ^ t := by
  apply causalSupport_card_le_pow G 0 t observer (nu * M)
  intro k e hk heq target selected
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  have hr : r < t := by omega
  have he : t - (r + 1) = e := by omega
  have heprev : t - r = e + 1 := by omega
  exact inDegree_le_visible_bounds G leader r e observer target nu M selected
    (by simpa only [heprev] using nodes r hr)
    (by simpa only [he, heprev] using labels r hr)

/-- The same input bounds control every intermediate causal support. -/
theorem support_card_le_pow {V : Type} [Fintype V]
    (G : Nat → V → V → Nat) (leader : V → Bool) (t r : Nat)
    (observer : V) (nu M : Nat) (within : r ≤ t)
    (nodes : ∀ k, k < t → (visibleNodes G leader k (t - k) observer).card ≤ nu)
    (labels : ∀ k, k < t → ∀ old ∈ visibleNodes G leader k (t - k) observer,
      ∀ new ∈ visibleNodes G leader (k + 1) (t - (k + 1)) observer,
        redMultiplicity G leader k old new ≤ M) :
    (causalSupport G r (t - r) observer).card ≤ (1 + nu * M) ^ (t - r) := by
  apply causalSupport_card_le_pow G r (t - r) observer (nu * M)
  intro k e hk heq target selected
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  have hj : j < t := by omega
  have he : t - (j + 1) = e := by omega
  have heprev : t - j = e + 1 := by omega
  exact inDegree_le_visible_bounds G leader j e observer target nu M selected
    (by simpa only [heprev] using nodes j hj)
    (by simpa only [he, heprev] using labels j hj)

/-- Every selected count is bounded by the same K used at the initial level. -/
theorem all_supports_card_le_initial_bound {V : Type} [Fintype V]
    (G : Nat → V → V → Nat) (leader : V → Bool) (t r : Nat)
    (observer : V) (nu M : Nat) (within : r ≤ t)
    (nodes : ∀ k, k < t → (visibleNodes G leader k (t - k) observer).card ≤ nu)
    (labels : ∀ k, k < t → ∀ old ∈ visibleNodes G leader k (t - k) observer,
      ∀ new ∈ visibleNodes G leader (k + 1) (t - (k + 1)) observer,
        redMultiplicity G leader k old new ≤ M) :
    (causalSupport G r (t - r) observer).card ≤ (1 + nu * M) ^ t := by
  exact (support_card_le_pow G leader t r observer nu M within nodes labels).trans
    (Nat.pow_le_pow_right (by omega) (Nat.sub_le t r))

/-- The number of nonroot nodes across all levels of the actual vista. -/
noncomputable def vistaNodeCount {V : Type} [Fintype V]
    (G : Nat → V → V → Nat) (leader : V → Bool) (t : Nat) (observer : V) : Nat :=
  ∑ r ∈ Finset.range (t + 1), (visibleNodes G leader r (t - r) observer).card

/-- A total explicit node count bounds each visible level's count. -/
theorem visible_card_le_vistaNodeCount {V : Type} [Fintype V]
    (G : Nat → V → V → Nat) (leader : V → Bool) (t r : Nat)
    (observer : V) (within : r ≤ t) :
    (visibleNodes G leader r (t - r) observer).card ≤ vistaNodeCount G leader t observer := by
  unfold vistaNodeCount
  exact Finset.single_le_sum (s := Finset.range (t + 1)) (a := r)
    (f := fun k ↦ (visibleNodes G leader k (t - k) observer).card)
    (fun _ _ ↦ Nat.zero_le _)
    (Finset.mem_range.mpr (by omega))

/-- Instantiating nu with the actual vista node count gives the support bound
without a separate node-count hypothesis. Root-inclusive encodings may use a
larger nu. Only visible incoming labels need the bound M. -/
theorem initial_support_bound_of_vista_labels {V : Type} [Fintype V]
    (G : Nat → V → V → Nat) (leader : V → Bool) (t : Nat)
    (observer : V) (M : Nat)
    (labels : ∀ r, r < t → ∀ old ∈ visibleNodes G leader r (t - r) observer,
      ∀ new ∈ visibleNodes G leader (r + 1) (t - (r + 1)) observer,
        redMultiplicity G leader r old new ≤ M) :
    (causalSupport G 0 t observer).card ≤
      (1 + vistaNodeCount G leader t observer * M) ^ t := by
  exact initial_support_card_le_pow G leader t observer _ M
    (fun r hr ↦ visible_card_le_vistaNodeCount G leader t r observer (by omega)) labels

end Counting.SupportBound
