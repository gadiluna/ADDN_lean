import Counting.RealizabilityCertificate
import Counting.TailExposure
import Counting.AllLeaders

namespace Counting.Realizability
open DirectedCounting PaperHistory
open TimingProtocolLocal

variable {V : Type} [Fintype V]
variable (G : ℕ → V → V → ℕ) (leader : V → Bool) (t : ℕ) (observer : V)

noncomputable def supportAt (r : ℕ) : Finset V := causalSupport G r (t - r) observer

noncomputable def selectedGroup (r : ℕ) (H : FullHistory r) : Finset V := by
  classical
  exact (supportAt G t observer r).filter (fun v => history G leader r v = H)

noncomputable def selectedCounts : Counts := fun r H => (selectedGroup G leader t observer r H).card

theorem actual_levels_eq_support_image (r : ℕ) (within : r ≤ t) :
    levels t (history G leader t observer) r =
      (supportAt G t observer r).image (history G leader r) := by
  rw [levels_eq_image G leader t r within observer]
  change ((supportAt G t observer r).image (classOf G leader r)).image (nodeHistory G leader r) = _
  rw [Finset.image_image]
  congr 1
  funext v
  exact nodeHistory_classOf G leader r v

theorem selected_history_visible (r : ℕ) (within : r ≤ t) (v : V)
    (selected : v ∈ supportAt G t observer r) :
    history G leader r v ∈ levels t (history G leader t observer) r := by
  rw [actual_levels_eq_support_image G leader t observer r within]
  exact Finset.mem_image.mpr ⟨v, selected, rfl⟩

theorem selectedCounts_positive_iff (r : ℕ) (within : r ≤ t) (H : FullHistory r) :
    0 < selectedCounts G leader t observer r H ↔ H ∈ levels t (history G leader t observer) r := by
  classical
  rw [selectedCounts, Finset.card_pos, actual_levels_eq_support_image G leader t observer r within]
  simp only [selectedGroup, Finset.Nonempty, Finset.mem_filter, Finset.mem_image]

theorem supportAt_nested (r : ℕ) (before : r < t) :
    supportAt G t observer (r + 1) ⊆ supportAt G t observer r := by
  have heq : t - (r + 1) + 1 = t - r := by omega
  simpa only [supportAt, heq] using causalSupport_backward_subset G r (t - (r + 1)) observer

theorem no_incoming_from_unselected (r : ℕ) (before : r < t) (a b : V)
    (outside : a ∉ supportAt G t observer r) (selected : b ∈ supportAt G t observer (r + 1)) :
    G (r + 1) a b = 0 := by
  have heq : t - (r + 1) + 1 = t - r := by omega
  by_contra hnonzero
  apply outside
  have member := (mem_causalSupport_succ G r (t - (r + 1)) observer a).mpr
    (Or.inr ⟨b, selected, Nat.pos_of_ne_zero hnonzero⟩)
  simpa only [supportAt, heq] using member

theorem actual_parent_visible (r : ℕ) (before : r < t) (H : FullHistory (r + 1))
    (visible : H ∈ levels t (history G leader t observer) (r + 1)) :
    TimingProtocolLocal.parent r H ∈ levels t (history G leader t observer) r := by
  rw [actual_levels_eq_support_image G leader t observer (r + 1) (by omega)] at visible
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp visible
  exact selected_history_visible G leader t observer r (by omega) a (supportAt_nested G t observer r before ha)

theorem selectedCounts_total (r : ℕ) (within : r ≤ t) :
    (∑ H ∈ levels t (history G leader t observer) r, selectedCounts G leader t observer r H) =
      (supportAt G t observer r).card := by
  exact (Finset.card_eq_sum_card_fiberwise (selected_history_visible G leader t observer r within)).symm

theorem selectedCounts_sum (r : ℕ) (nodes : Finset (FullHistory r)) (f : FullHistory r → ℕ) :
    (∑ H ∈ nodes, selectedCounts G leader t observer r H * f H) =
      ∑ a ∈ (supportAt G t observer r).filter (fun a => history G leader r a ∈ nodes), f (history G leader r a) := by
  calc
    _ = ∑ H ∈ nodes, ∑ a ∈ (supportAt G t observer r).filter (fun a => history G leader r a = H),
        f (history G leader r a) := by
      apply Finset.sum_congr rfl
      intro H _
      symm
      calc
        _ = ∑ _a ∈ (supportAt G t observer r).filter (fun a => history G leader r a = H), f H := by
          exact Finset.sum_congr rfl (fun a ha => congrArg f (Finset.mem_filter.mp ha).2)
        _ = _ := by simp [selectedCounts, selectedGroup]
    _ = _ := Finset.sum_fiberwise_eq_sum_filter _ nodes (history G leader r) _

noncomputable def retainedGroup (r : ℕ) (H : FullHistory r) : Finset V := by
  classical
  exact (supportAt G t observer (r + 1)).filter (fun v => history G leader r v = H)

theorem retainedGroup_subset (r : ℕ) (before : r < t) (H : FullHistory r) :
    retainedGroup G leader t observer r H ⊆ selectedGroup G leader t observer r H := by
  intro a ha
  obtain ⟨hselected, hhistory⟩ := Finset.mem_filter.mp ha
  exact Finset.mem_filter.mpr ⟨supportAt_nested G t observer r before hselected, hhistory⟩

theorem childCount_eq_retained_card (r : ℕ) (before : r < t) (H : FullHistory r) :
    childCount (levels t (history G leader t observer)) (selectedCounts G leader t observer) r H =
      (retainedGroup G leader t observer r H).card := by
  classical
  unfold childCount
  rw [show (∑ v ∈ children (levels t (history G leader t observer)) r H,
      selectedCounts G leader t observer (r + 1) v) =
      ((supportAt G t observer (r + 1)).filter (fun a => history G leader (r + 1) a ∈
        children (levels t (history G leader t observer)) r H)).card from
    Finset.sum_card_fiberwise_eq_card_filter _ _ (history G leader (r + 1))]
  congr 1
  ext a
  simp only [Finset.mem_filter, children, retainedGroup]
  constructor
  · rintro ⟨ha, _, heq⟩
    exact ⟨ha, heq⟩
  · rintro ⟨ha, heq⟩
    exact ⟨ha, selected_history_visible G leader t observer (r + 1) (by omega) a ha, heq⟩

theorem selectedCounts_refinement (r : ℕ) (before : r < t) (H : FullHistory r) :
    childCount (levels t (history G leader t observer)) (selectedCounts G leader t observer) r H ≤
      selectedCounts G leader t observer r H := by
  rw [childCount_eq_retained_card G leader t observer r before]
  exact Finset.card_le_card (retainedGroup_subset G leader t observer r before H)

theorem leaving_eq_difference_card [DecidableEq V] (r : ℕ) (before : r < t) (H : FullHistory r) :
    leaving (levels t (history G leader t observer)) (selectedCounts G leader t observer) r H =
      ((selectedGroup G leader t observer r H) \ (retainedGroup G leader t observer r H)).card := by
  classical
  rw [Finset.card_sdiff_of_subset (retainedGroup_subset G leader t observer r before H)]
  exact congrArg (selectedCounts G leader t observer r H - ·) (childCount_eq_retained_card G leader t observer r before H)

theorem no_leaving_iff_groups_eq (r : ℕ) (before : r < t) (H : FullHistory r) :
    leaving (levels t (history G leader t observer)) (selectedCounts G leader t observer) r H = 0 ↔
      retainedGroup G leader t observer r H = selectedGroup G leader t observer r H := by
  have subset := retainedGroup_subset G leader t observer r before H
  unfold leaving
  rw [childCount_eq_retained_card G leader t observer r before]
  change (selectedGroup G leader t observer r H).card - (retainedGroup G leader t observer r H).card = 0 ↔ _
  constructor
  · intro hz
    exact Finset.eq_of_subset_of_card_le subset (Nat.sub_eq_zero_iff_le.mp hz)
  · intro heq
    rw [heq, Nat.sub_self]

theorem selectedCounts_bottom : selectedCounts G leader t observer t (history G leader t observer) = 1 := by
  classical
  change ((supportAt G t observer t).filter (fun v => history G leader t v = history G leader t observer)).card = 1
  have hs : supportAt G t observer t = {observer} := by simp [supportAt]
  rw [hs]
  rw [Finset.filter_eq_self.mpr (by intro a ha; rw [Finset.mem_singleton.mp ha])]
  exact Finset.card_singleton _

theorem initialCount_bound (b : Bool) :
    initialCount (levels t (history G leader t observer)) (selectedCounts G leader t observer) b ≤
      (Finset.univ.filter (fun v => leader v = b)).card := by
  classical
  unfold initialCount
  split
  · apply Finset.card_le_card
    intro v hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ v, (Finset.mem_filter.mp hv).2⟩
  · exact Nat.zero_le _

end Counting.Realizability
