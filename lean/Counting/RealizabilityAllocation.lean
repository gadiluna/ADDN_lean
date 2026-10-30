import Counting.RealizabilityCertificate
import Counting.CountAllocation

namespace Counting.Realizability
open DirectedCounting TimingProtocolLocal

variable {ell N t : ℕ} {H : FullHistory t} {k : Counts}

noncomputable def Certificate.nodeParent (cert : Certificate ell N t H k) (r : ℕ)
    (v : VisibleNode (levels t H) (r + 1)) : VisibleNode (levels t H) r :=
  ⟨parent r v.val, by
    by_cases hr : r < t
    · exact cert.parent_visible r hr v.val v.property
    · have hv := v.property
      simp [levels, show ¬ r + 1 ≤ t by omega] at hv⟩

theorem Certificate.nodeParent_val (cert : Certificate ell N t H k) (r : ℕ)
    (v : VisibleNode (levels t H) (r + 1)) :
    (cert.nodeParent r v).val = parent r v.val := rfl

theorem Certificate.allocation_bound (cert : Certificate ell N t H k) (r : ℕ)
    (u : VisibleNode (levels t H) r) :
    (∑ v ∈ Finset.univ.filter (fun v => cert.nodeParent r v = u), k (r + 1) v.val) ≤ k r u.val := by
  classical
  have sum_eq : (∑ v ∈ Finset.univ.filter (fun v => cert.nodeParent r v = u), k (r + 1) v.val) =
      childCount (levels t H) k r u.val := by
    simp only [childCount, children, Finset.sum_filter]
    change (∑ v : VisibleNode (levels t H) (r + 1),
      if cert.nodeParent r v = u then k (r + 1) v.val else 0) = _
    simp only [Subtype.ext_iff, Certificate.nodeParent_val]
    exact Finset.sum_coe_sort (levels t H (r + 1)) (fun v => if parent r v = u.val then k (r + 1) v else 0)
  rw [sum_eq]
  by_cases hr : r < t
  · exact cert.refinement r hr u.val u.property
  · have empty : levels t H (r + 1) = ∅ := by simp [levels, show ¬ r + 1 ≤ t by omega]
    simp [childCount, children, empty]

theorem initial_sum_eq (b : Bool) :
    (∑ u ∈ Finset.univ.filter (fun u : VisibleNode (levels t H) 0 => u.val = b), k 0 u.val) =
      initialCount (levels t H) k b := by
  classical
  simp only [Finset.sum_filter, initialCount]
  change (∑ u : VisibleNode (levels t H) 0, if u.val = b then k 0 u.val else 0) = _
  exact (Finset.sum_coe_sort (levels t H 0) (fun u => if u = (b : FullHistory 0) then k 0 u else 0)).trans
    (Finset.sum_ite_eq' (levels t H 0) b (k 0))

theorem Certificate.initial_allocation (cert : Certificate ell N t H k) :
    ∃ initial : CountAllocation.Slots (fun u : VisibleNode (levels t H) 0 => k 0 u.val) ↪
      CountAllocation.Population N ell,
      ∀ i, CountAllocation.populationLeader N ell (initial i) = i.1.val := by
  refine CountAllocation.exists_initial_allocation (C := VisibleNode (levels t H) 0)
    (fun u => k 0 u.val) (fun u => u.val) N ell ?_ ?_
  · convert (initial_sum_eq (H := H) (k := k) true).le.trans cert.initial_leaders using 1
    · rfl
    · apply Finset.sum_congr
      · ext u
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rfl
      · intro u _
        rfl
  · convert (initial_sum_eq (H := H) (k := k) false).le.trans cert.initial_nonleaders using 1
    · rfl
    · apply Finset.sum_congr
      · ext u
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rfl
      · intro u _
        rfl

/-- The selected-count inequalities of the actual certificate instantiate
the nested allocation construction without any additional feasibility
hypothesis. The initial placement has exactly the required input labels. -/
noncomputable def Certificate.initialEmbedding (cert : Certificate ell N t H k) :
    CountAllocation.Slots (fun u : VisibleNode (levels t H) 0 => k 0 u.val) ↪
      CountAllocation.Population N ell := Classical.choose cert.initial_allocation

theorem Certificate.initialEmbedding_label (cert : Certificate ell N t H k)
    (i : CountAllocation.Slots (fun u : VisibleNode (levels t H) 0 => k 0 u.val)) :
    CountAllocation.populationLeader N ell (cert.initialEmbedding i) = i.1.val :=
  Classical.choose_spec cert.initial_allocation i

noncomputable def Certificate.allocation (cert : Certificate ell N t H k) (r : ℕ) :
    CountAllocation.Slots (fun u : VisibleNode (levels t H) r => k r u.val) ↪
      CountAllocation.Population N ell :=
  CountAllocation.allocation cert.nodeParent (fun r u => k r u.val)
    cert.allocation_bound cert.initialEmbedding r

noncomputable def Certificate.selected (cert : Certificate ell N t H k) (r : ℕ) :
    Finset (CountAllocation.Population N ell) :=
  CountAllocation.selected cert.nodeParent (fun r u => k r u.val)
    cert.allocation_bound cert.initialEmbedding r

noncomputable def Certificate.group (cert : Certificate ell N t H k) (r : ℕ)
    (u : VisibleNode (levels t H) r) : Finset (CountAllocation.Population N ell) :=
  CountAllocation.group cert.nodeParent (fun r u => k r u.val)
    cert.allocation_bound cert.initialEmbedding r u

theorem Certificate.selected_nested (cert : Certificate ell N t H k) (r : ℕ) :
    cert.selected (r + 1) ⊆ cert.selected r :=
  CountAllocation.selected_nested _ _ _ _ r

theorem Certificate.group_card (cert : Certificate ell N t H k) (r : ℕ)
    (u : VisibleNode (levels t H) r) : (cert.group r u).card = k r u.val :=
  CountAllocation.group_card _ _ _ _ r u

theorem Certificate.selected_card (cert : Certificate ell N t H k) (r : ℕ) :
    (cert.selected r).card = ∑ u ∈ levels t H r, k r u := by
  rw [Certificate.selected, CountAllocation.selected_card]
  exact Finset.sum_coe_sort _ _

theorem Certificate.group_subset_parent (cert : Certificate ell N t H k) (r : ℕ)
    (u : VisibleNode (levels t H) (r + 1)) :
    cert.group (r + 1) u ⊆ cert.group r (cert.nodeParent r u) :=
  CountAllocation.group_subset_parent _ _ _ _ r u

theorem Certificate.groups_disjoint (cert : Certificate ell N t H k) (r : ℕ)
    {u v : VisibleNode (levels t H) r} (different : u ≠ v) :
    Disjoint (cert.group r u) (cert.group r v) :=
  CountAllocation.groups_disjoint _ _ _ _ r different

theorem Certificate.group_subset_selected (cert : Certificate ell N t H k) (r : ℕ)
    (u : VisibleNode (levels t H) r) : cert.group r u ⊆ cert.selected r :=
  CountAllocation.group_subset_selected _ _ _ _ r u

theorem Certificate.selected_eq_union_groups (cert : Certificate ell N t H k) (r : ℕ) :
    cert.selected r = Finset.univ.biUnion (cert.group r) := by
  classical
  exact CountAllocation.selected_eq_union_groups _ _ _ _ r

theorem Certificate.selected_total_le (cert : Certificate ell N t H k) (r : ℕ) :
    (∑ u ∈ levels t H r, k r u) ≤ N := by
  rw [← cert.selected_card r]
  exact (Finset.card_le_univ _).trans_eq (CountAllocation.population_card N ell cert.order_ge_leaders)

theorem Certificate.count_le_order (cert : Certificate ell N t H k) (r : ℕ)
    (u : VisibleNode (levels t H) r) : k r u.val ≤ N := by
  rw [← cert.group_card r u]
  exact (Finset.card_le_univ _).trans_eq (CountAllocation.population_card N ell cert.order_ge_leaders)

theorem Certificate.group_nonempty (cert : Certificate ell N t H k) (r : ℕ)
    (within : r ≤ t) (u : VisibleNode (levels t H) r) : (cert.group r u).Nonempty := by
  rw [← Finset.card_pos, cert.group_card]
  exact cert.positive r within u.val u.property

theorem input_parent (r : ℕ) (v : FullHistory (r + 1)) :
    input r (parent r v) = input (r + 1) v := by
  have cast_fst (a b : ℕ) (eq : a = b) (w : FullHistory (a + 1)) :
      (cast (congrArg FullHistory (congrArg (· + 1) eq)) w).1 =
        cast (congrArg FullHistory eq) w.1 := by
    cases eq
    rfl
  simp only [input, ancestor, Nat.zero_le, dif_pos, Nat.sub_zero, blackAncestor, parent]
  exact congrArg (blackAncestor 0 r) (cast_fst r (0 + r) (Nat.zero_add r).symm v).symm

theorem input_zero (v : FullHistory 0) : input 0 v = v := rfl

theorem Certificate.allocation_label (cert : Certificate ell N t H k) (r : ℕ)
    (i : CountAllocation.Slots (fun u : VisibleNode (levels t H) r => k r u.val)) :
    CountAllocation.populationLeader N ell (cert.allocation r i) = input r i.1.val := by
  apply CountAllocation.allocation_label cert.nodeParent (fun r u => k r u.val)
    cert.allocation_bound cert.initialEmbedding (fun r u => input r u.val)
    (CountAllocation.populationLeader N ell)
  · intro r u
    exact input_parent r u.val
  · intro i
    exact cert.initialEmbedding_label i

theorem Certificate.group_label (cert : Certificate ell N t H k) (r : ℕ)
    (u : VisibleNode (levels t H) r) (a : CountAllocation.Population N ell)
    (ha : a ∈ cert.group r u) : CountAllocation.populationLeader N ell a = input r u.val := by
  classical
  simp only [Certificate.group, CountAllocation.group, Finset.mem_image, Finset.mem_univ, true_and] at ha
  obtain ⟨j, hj⟩ := ha
  exact (congrArg (CountAllocation.populationLeader N ell) hj.symm).trans (cert.allocation_label r ⟨u, j⟩)

end Counting.Realizability
