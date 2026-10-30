import Counting.RealizabilityAllocation
import Counting.RealizabilityConstructionGraph

namespace Counting.Realizability
open DirectedCounting TimingProtocolLocal
open RealizabilityConstruction

variable {ell N t : ℕ} {H : FullHistory t} {k : Counts}

/-- Selected physical agents are tagged by their unique allocated visible
node. The tag is absent for unselected agents. -/
noncomputable def Certificate.tag (cert : Certificate ell N t H k) (r : ℕ)
    (a : CountAllocation.Population N ell) : Option (VisibleNode (levels t H) r) :=
  if h : ∃ u, a ∈ cert.group r u then some (Classical.choose h) else none

theorem Certificate.tag_some_iff (cert : Certificate ell N t H k) (r : ℕ)
    (a : CountAllocation.Population N ell) (u : VisibleNode (levels t H) r) :
    cert.tag r a = some u ↔ a ∈ cert.group r u := by
  classical
  unfold Certificate.tag
  split
  · rename_i h
    have mem := Classical.choose_spec h
    constructor
    · intro eq
      exact (Option.some.inj eq) ▸ mem
    · intro hu
      congr 1
      by_contra different
      exact Finset.disjoint_left.mp (cert.groups_disjoint r different) mem hu
  · rename_i h
    constructor
    · intro heq
      cases heq
    · intro hu
      exact (h ⟨u, hu⟩).elim

theorem Certificate.tag_none_iff (cert : Certificate ell N t H k) (r : ℕ)
    (a : CountAllocation.Population N ell) : cert.tag r a = none ↔ a ∉ cert.selected r := by
  classical
  rw [cert.selected_eq_union_groups]
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
  unfold Certificate.tag
  split <;> simp_all

theorem Certificate.tag_nested (cert : Certificate ell N t H k) (r : ℕ)
    (a : CountAllocation.Population N ell) (v : VisibleNode (levels t H) (r + 1))
    (selected : cert.tag (r + 1) a = some v) : cert.tag r a = some (cert.nodeParent r v) :=
  (cert.tag_some_iff r a _).mpr (cert.group_subset_parent r v ((cert.tag_some_iff (r + 1) a v).mp selected))

theorem Certificate.tag_sum (cert : Certificate ell N t H k) (r : ℕ)
    (f : VisibleNode (levels t H) r → ℕ) :
    (∑ u : VisibleNode (levels t H) r, k r u.val * f u) =
      ∑ a : CountAllocation.Population N ell, (cert.tag r a).elim 0 f := by
  classical
  calc
    _ = ∑ u : VisibleNode (levels t H) r, ∑ a ∈ cert.group r u, (cert.tag r a).elim 0 f := by
      apply Finset.sum_congr rfl
      intro u _
      rw [show (∑ a ∈ cert.group r u, (cert.tag r a).elim 0 f) = ∑ _a ∈ cert.group r u, f u from
        Finset.sum_congr rfl (fun a ha => by rw [(cert.tag_some_iff r a u).mpr ha]; rfl)]
      simp [cert.group_card]
    _ = ∑ a ∈ cert.selected r, (cert.tag r a).elim 0 f := by
      rw [cert.selected_eq_union_groups, Finset.sum_biUnion]
      intro u _ v _ hne
      exact cert.groups_disjoint r hne
    _ = _ := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro a _ outside
      rw [(cert.tag_none_iff r a).mpr outside]
      rfl

noncomputable def Certificate.roundData (cert : Certificate ell N t H k) (r : ℕ) :
    RoundData (CountAllocation.Population N ell)
      (VisibleNode (levels t H) r) (VisibleNode (levels t H) (r + 1)) where
  old := cert.tag r
  new := cert.tag (r + 1)
  parent := cert.nodeParent r
  degree := fun v => degree r v.val
  red := fun u v => red r u.val v.val
  nested := cert.tag_nested r

theorem Certificate.round_supply (cert : Certificate ell N t H k) (r : ℕ)
    (u : VisibleNode (levels t H) r) :
    (cert.roundData r).supply u = supply (levels t H) k r u.val := by
  classical
  have sum := cert.tag_sum (r + 1) (fun v => if cert.nodeParent r v = u then degree r v.val else 0)
  have equal : (cert.roundData r).supply u = ∑ a : CountAllocation.Population N ell,
      (cert.tag (r + 1) a).elim 0 (fun v => if cert.nodeParent r v = u then degree r v.val else 0) := by
    apply Finset.sum_congr rfl
    intro a _
    cases hn : cert.tag (r + 1) a <;> simp [RoundData.retainedSupply, Certificate.roundData, hn]
  rw [equal, ← sum]
  simp only [supply, children, Finset.sum_filter, mul_ite, Nat.mul_zero, Subtype.ext_iff, Certificate.nodeParent_val]
  exact Finset.sum_coe_sort (levels t H (r + 1))
    (fun v => if parent r v = u.val then k (r + 1) v * degree r v else 0)

theorem Certificate.round_demand (cert : Certificate ell N t H k) (r : ℕ)
    (u : VisibleNode (levels t H) r) :
    (cert.roundData r).demand u = demand (levels t H) k r u.val := by
  classical
  have equal : (cert.roundData r).demand u = ∑ a : CountAllocation.Population N ell,
      (cert.tag (r + 1) a).elim 0 (fun v => red r u.val v.val) := by
    apply Finset.sum_congr rfl
    intro a _
    cases hn : cert.tag (r + 1) a <;> simp [RoundData.requiredReceipt, Certificate.roundData, hn]
  rw [equal, ← cert.tag_sum]
  exact Finset.sum_coe_sort (levels t H (r + 1)) (fun v => k (r + 1) v * red r u.val v)

theorem Certificate.round_outside (cert : Certificate ell N t H k) (r : ℕ) :
    (cert.roundData r).outside = Finset.univ \ cert.selected (r + 1) := by
  classical
  ext a
  simp only [RoundData.outside, Certificate.roundData, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_sdiff]
  exact cert.tag_none_iff (r + 1) a

theorem Certificate.round_hidden (cert : Certificate ell N t H k) (r : ℕ) :
    (cert.roundData r).outside.card = hidden N (levels t H) k r := by
  classical
  rw [cert.round_outside, Finset.card_sdiff_of_subset (Finset.subset_univ _),
    Finset.card_univ, CountAllocation.population_card N ell cert.order_ge_leaders, cert.selected_card]
  rfl

theorem Certificate.round_leaving (cert : Certificate ell N t H k) (r : ℕ)
    (u : VisibleNode (levels t H) r) :
    (cert.roundData r).leaving u = cert.group r u \ cert.selected (r + 1) := by
  classical
  ext a
  simp only [RoundData.leaving, RoundData.outside, Certificate.roundData, Finset.mem_filter,
    Finset.mem_univ, true_and, Finset.mem_sdiff]
  rw [cert.tag_none_iff, cert.tag_some_iff]
  exact and_comm

theorem Certificate.retained_card (cert : Certificate ell N t H k) (r : ℕ)
    (u : VisibleNode (levels t H) r) :
    (cert.selected (r + 1) ∩ cert.group r u).card = childCount (levels t H) k r u.val := by
  classical
  have tags := cert.tag_sum (r + 1) (fun v => if cert.nodeParent r v = u then 1 else 0)
  have left : (∑ v : VisibleNode (levels t H) (r + 1),
      k (r + 1) v.val * (if cert.nodeParent r v = u then 1 else 0)) = childCount (levels t H) k r u.val := by
    simp only [childCount, children, Finset.sum_filter, mul_ite, Nat.mul_one, Nat.mul_zero,
      Subtype.ext_iff, Certificate.nodeParent_val]
    exact Finset.sum_coe_sort (levels t H (r + 1)) (fun v => if parent r v = u.val then k (r + 1) v else 0)
  have right : (∑ a : CountAllocation.Population N ell,
      (cert.tag (r + 1) a).elim 0 (fun v => if cert.nodeParent r v = u then 1 else 0)) =
      (cert.selected (r + 1) ∩ cert.group r u).card := by
    calc
      _ = ∑ a : CountAllocation.Population N ell,
          if a ∈ cert.selected (r + 1) ∩ cert.group r u then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro a _
        cases hn : cert.tag (r + 1) a with
        | none =>
          have outside := (cert.tag_none_iff (r + 1) a).mp hn
          simp [outside]
        | some v =>
          have member := (cert.tag_some_iff (r + 1) a v).mp hn
          have selected := cert.group_subset_selected (r + 1) v member
          have old := cert.tag_nested r a v hn
          have eq : a ∈ cert.group r u ↔ cert.nodeParent r v = u := by
            rw [← cert.tag_some_iff, old, Option.some.injEq]
          simp only [Option.elim_some, Finset.mem_inter, selected, true_and, eq]
      _ = _ := by simp only [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter, Nat.cast_id]
  exact right.symm.trans (tags.symm.trans left)

theorem Certificate.round_leaving_card (cert : Certificate ell N t H k) (r : ℕ)
    (u : VisibleNode (levels t H) r) :
    ((cert.roundData r).leaving u).card = leaving (levels t H) k r u.val := by
  classical
  rw [cert.round_leaving, Finset.card_sdiff, cert.group_card, cert.retained_card]
  rfl

theorem Certificate.round_center_none_iff (cert : Certificate ell N t H k) (r : ℕ) :
    (cert.roundData r).center = none ↔ hidden N (levels t H) k r = 0 := by
  rw [RoundData.center, RoundData.pick_none_iff, ← Finset.card_pos, cert.round_hidden]
  omega

theorem Certificate.round_leaver_none_iff (cert : Certificate ell N t H k) (r : ℕ)
    (u : VisibleNode (levels t H) r) :
    (cert.roundData r).leaver u = none ↔ leaving (levels t H) k r u.val = 0 := by
  rw [RoundData.leaver, RoundData.pick_none_iff, ← Finset.card_pos, cert.round_leaving_card]
  omega

/-- The certificate's two arithmetic balance tests are exactly those
needed to balance every auxiliary vertex of the expanded physical graph. -/
theorem Certificate.round_balanced (cert : Certificate ell N t H k) (r : ℕ) (before : r < t) :
    (cert.roundData r).Balanced where
  full := by
    intro center u
    rw [cert.round_supply, cert.round_demand]
    exact cert.balance_full r before ((cert.round_center_none_iff r).mp center) u.val u.property
  proper := by
    intro center u leaver
    rw [cert.round_supply, cert.round_demand]
    exact cert.balance_no_leaving r before
      (Nat.pos_of_ne_zero (fun hz => center ((cert.round_center_none_iff r).mpr hz)))
      u.val u.property ((cert.round_leaver_none_iff r u).mp leaver)

end Counting.Realizability
