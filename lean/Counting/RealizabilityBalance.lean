import Counting.RealizabilitySelected

namespace Counting.Realizability
open DirectedCounting TimingProtocolLocal

variable {V : Type} [Fintype V]
variable (G : ℕ → V → V → ℕ) (leader : V → Bool) (t : ℕ) (observer : V)

theorem selected_supply (r : ℕ) (before : r < t) (H : FullHistory r) :
    supply (levels t (history G leader t observer)) (selectedCounts G leader t observer) r H =
      weightedEdgeCount (G (r + 1)) (retainedGroup G leader t observer r H) Finset.univ := by
  classical
  unfold supply
  rw [selectedCounts_sum, weightedEdgeCount_transpose]
  have same : (supportAt G t observer (r + 1)).filter (fun a => history G leader (r + 1) a ∈
      children (levels t (history G leader t observer)) r H) = retainedGroup G leader t observer r H := by
    ext a
    simp only [Finset.mem_filter, children, retainedGroup]
    exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1,
      selected_history_visible G leader t observer (r + 1) (by omega) a h.1, h.2⟩⟩
  rw [same]
  rfl

theorem selected_red (r : ℕ) (before : r < t) (H : FullHistory r) (b : V)
    (selected : b ∈ supportAt G t observer (r + 1)) :
    red r H (history G leader (r + 1) b) =
      weightedIncomingCount (G (r + 1)) (selectedGroup G leader t observer r H) b := by
  classical
  change (incoming (G (r + 1)) (history G leader r) b).count H = _
  rw [count_incoming]
  unfold weightedIncomingCount selectedGroup
  rw [Finset.sum_filter]
  calc
    _ = ∑ a ∈ supportAt G t observer r, if history G leader r a = H then G (r + 1) a b else 0 := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro a _ outside
      rw [no_incoming_from_unselected G t observer r before a b outside selected]
      simp
    _ = _ := rfl

theorem selected_demand (r : ℕ) (before : r < t) (H : FullHistory r) :
    demand (levels t (history G leader t observer)) (selectedCounts G leader t observer) r H =
      weightedEdgeCount (G (r + 1)) (selectedGroup G leader t observer r H)
        (supportAt G t observer (r + 1)) := by
  classical
  unfold demand
  rw [selectedCounts_sum]
  have same : (supportAt G t observer (r + 1)).filter (fun a => history G leader (r + 1) a ∈
      levels t (history G leader t observer) (r + 1)) = supportAt G t observer (r + 1) :=
    Finset.filter_eq_self.mpr (selected_history_visible G leader t observer (r + 1) (by omega))
  rw [same]
  exact Finset.sum_congr rfl (fun b hb => selected_red G leader t observer r before H b hb)

theorem selected_hidden (r : ℕ) (before : r < t) :
    hidden (Fintype.card V) (levels t (history G leader t observer)) (selectedCounts G leader t observer) r =
      Fintype.card V - (supportAt G t observer (r + 1)).card := by
  unfold hidden
  rw [selectedCounts_total G leader t observer (r + 1) (by omega)]

theorem selected_hidden_zero_iff (r : ℕ) (before : r < t) :
    hidden (Fintype.card V) (levels t (history G leader t observer)) (selectedCounts G leader t observer) r = 0 ↔
      supportAt G t observer (r + 1) = Finset.univ := by
  classical
  rw [selected_hidden G leader t observer r before, Nat.sub_eq_zero_iff_le]
  exact ⟨fun h => Finset.eq_of_subset_of_card_le (Finset.subset_univ _) (by simpa using h),
    fun h => by simp [h]⟩

theorem selected_balance_full (r : ℕ) (before : r < t)
    (full : hidden (Fintype.card V) (levels t (history G leader t observer)) (selectedCounts G leader t observer) r = 0)
    (H : FullHistory r) :
    supply (levels t (history G leader t observer)) (selectedCounts G leader t observer) r H =
      demand (levels t (history G leader t observer)) (selectedCounts G leader t observer) r H := by
  classical
  have hn := (selected_hidden_zero_iff G leader t observer r before).mp full
  have ho : supportAt G t observer r = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro a
    exact supportAt_nested G t observer r before (by rw [hn]; exact Finset.mem_univ _)
  rw [selected_supply G leader t observer r before H, selected_demand G leader t observer r before H]
  simp only [retainedGroup, selectedGroup, hn, ho]

theorem selected_balance_no_leaving (r : ℕ) (before : r < t) (H : FullHistory r)
    (none : leaving (levels t (history G leader t observer)) (selectedCounts G leader t observer) r H = 0) :
    demand (levels t (history G leader t observer)) (selectedCounts G leader t observer) r H ≤
      supply (levels t (history G leader t observer)) (selectedCounts G leader t observer) r H := by
  rw [selected_supply G leader t observer r before H, selected_demand G leader t observer r before H,
    (no_leaving_iff_groups_eq G leader t observer r before H).mp none]
  exact weightedEdgeCount_mono_targets _ _ (Finset.subset_univ _)

theorem selected_supply_gt_demand (r : ℕ) (before : r < t) (H : FullHistory r)
    (none : leaving (levels t (history G leader t observer)) (selectedCounts G leader t observer) r H = 0)
    (a b : V) (ha : a ∈ retainedGroup G leader t observer r H)
    (hb : b ∉ supportAt G t observer (r + 1)) (edge : 0 < G (r + 1) a b) :
    demand (levels t (history G leader t observer)) (selectedCounts G leader t observer) r H <
      supply (levels t (history G leader t observer)) (selectedCounts G leader t observer) r H := by
  have le := selected_balance_no_leaving G leader t observer r before H none
  apply lt_of_le_of_ne le
  intro eq
  have hn := (no_leaving_iff_groups_eq G leader t observer r before H).mp none
  rw [selected_supply G leader t observer r before H, selected_demand G leader t observer r before H, hn] at eq
  have zero := ShortAudit.no_arc_of_edge_count_eq (G (r + 1))
    (selectedGroup G leader t observer r H) (supportAt G t observer (r + 1)) eq.symm a (hn ▸ ha) b hb
  omega

end Counting.Realizability
