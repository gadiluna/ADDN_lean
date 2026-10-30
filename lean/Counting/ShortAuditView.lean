import Counting.ShortAudit
import Counting.CoreTiming
import Counting.SupportBound
import Counting.ForwardFibers

namespace Counting.ShortAudit
open DirectedCounting PaperHistory

variable {V : Type} [Fintype V]
variable (G : ℕ → V → V → ℕ) (leader : V → Bool)

/-- The agents represented by selected full history fibers. -/
noncomputable def agents (r : ℕ) (nodes : Finset (Node G leader r)) : Finset V := by
  classical
  exact Finset.univ.filter (fun v => classOf G leader r v ∈ nodes)

@[simp] theorem mem_agents (r : ℕ) (nodes : Finset (Node G leader r)) (v : V) :
    v ∈ agents G leader r nodes ↔ classOf G leader r v ∈ nodes := by
  classical
  simp [agents]

theorem agents_card (r : ℕ) (nodes : Finset (Node G leader r)) :
    (agents G leader r nodes).card = ∑ i ∈ nodes, anonymity G leader r i :=
  (sum_anonymity_eq_card_filter G leader r nodes).symm

theorem agents_refine (r s : ℕ) (hrs : r ≤ s) (visible : ∀ r, Finset (Node G leader r))
    (parents : ∀ k, k < s → ∀ i ∈ visible (k + 1), parent G leader k i ∈ visible k) :
    agents G leader s (visible s) ⊆ agents G leader r (visible r) := by
  intro v hv
  have ha := CoreHistory.ancestor_visible_of_parent_visible G leader r s hrs visible parents
    (classOf G leader s v) ((mem_agents G leader s _ v).mp hv)
  rw [CoreHistory.ancestor_classOf G leader r s hrs] at ha
  exact (mem_agents G leader r _ v).mpr ha

/-- H2 for actual vistas: every positive red predecessor of a visible node
is visible one level earlier, even when a different member witnesses visibility. -/
theorem red_predecessor_visible (r d : ℕ) (observer : V)
    (p : Node G leader r) (c : Node G leader (r + 1))
    (hc : c ∈ visibleNodes G leader (r + 1) d observer)
    (red : 0 < redMultiplicity G leader r p c) :
    p ∈ visibleNodes G leader r (d + 1) observer := by
  classical
  obtain ⟨v, hvfiber, hvselected⟩ := (visible_iff_fiber_meets_support G leader (r + 1) d observer c).mp hc
  have hsum : 0 < ∑ a ∈ fiber G leader r p, G (r + 1) a v := by
    change 0 < weightedIncomingCount (G (r + 1)) (fiber G leader r p) v
    rwa [incoming_eq_redMultiplicity G leader r p c hvfiber]
  obtain ⟨a, ha, harc⟩ := Finset.sum_pos_iff.mp hsum
  have hvisible := SupportBound.incoming_source_visible G leader r d observer a v hvselected harc
  simpa only [(mem_fiber G leader r p a).mp ha] using hvisible

theorem red_predecessor_visible_at_round (round r : ℕ) (before : r < round) (observer : V)
    (p : Node G leader r) (c : Node G leader (r + 1))
    (hc : c ∈ CoreTiming.levelsAt G leader round observer (r + 1))
    (red : 0 < redMultiplicity G leader r p c) :
    p ∈ CoreTiming.levelsAt G leader round observer r := by
  have hv := red_predecessor_visible G leader r (round - (r + 1)) observer p c hc red
  have heq : round - (r + 1) + 1 = round - r := by omega
  simpa only [CoreTiming.levelsAt, heq] using hv

/-- A proper represented population cannot stay unchanged across adjacent
visible levels: an incoming cut edge would expose an outside predecessor. -/
theorem agents_strict_refinement (round r : ℕ) (before : r < round) (observer : V)
    (connected : StronglyConnected (fun u v => 0 < G (r + 1) u v))
    (proper : agents G leader r (CoreTiming.levelsAt G leader round observer r) ≠ Finset.univ) :
    agents G leader (r + 1) (CoreTiming.levelsAt G leader round observer (r + 1)) ≠
      agents G leader r (CoreTiming.levelsAt G leader round observer r) := by
  classical
  let S := agents G leader r (CoreTiming.levelsAt G leader round observer r)
  have hmissing : ∃ a, a ∉ S := by
    by_contra hn
    push Not at hn
    exact proper (Finset.eq_univ_of_forall hn)
  have hobserver : observer ∈ S := by
    apply (mem_agents G leader r _ observer).mpr
    exact Finset.mem_image.mpr ⟨observer, observer_mem_causalSupport G r (round - r) observer, rfl⟩
  obtain ⟨a, b, ha, hb, hab⟩ := exists_edge_leaving connected
    (Q := {v | v ∉ S}) hmissing ⟨observer, by simpa using hobserver⟩
  have hbS : b ∈ S := by simpa using hb
  intro heq
  have hbnext : classOf G leader (r + 1) b ∈ CoreTiming.levelsAt G leader round observer (r + 1) := by
    apply (mem_agents G leader (r + 1) _ b).mp
    rw [heq]
    exact hbS
  have hred : 0 < redMultiplicity G leader r (classOf G leader r a) (classOf G leader (r + 1) b) := by
    rw [← incoming_eq_redMultiplicity G leader r _ _ (show b ∈ fiber G leader (r + 1) (classOf G leader (r + 1) b) by simp)]
    exact lt_of_lt_of_le hab (Finset.single_le_sum (f := fun v => G (r + 1) v b)
      (fun _ _ => Nat.zero_le _) (show a ∈ fiber G leader r (classOf G leader r a) by simp))
  exact ha ((mem_agents G leader r _ a).mpr
    (red_predecessor_visible_at_round G leader round r before observer _ _ hbnext hred))

namespace Checks
variable {G leader} {m h : ℕ} {candidate : ∀ r, Node G leader r → ℕ}
  {observer : V}
  (C : Checks G leader m h (CoreTiming.levelsAt G leader (2 * m - 2) observer) candidate)

include C

/-- Tail exposure and the singleton conclusion force the exact represented
population and candidate values at the anchor of a false short audit. -/
theorem false_anchor_rigidity (small : m < Fintype.card V)
    (connected : ∀ t, 0 < t → StronglyConnected (fun u v => 0 < G t u v)) :
    (∀ u ∈ CoreTiming.levelsAt G leader (2 * m - 2) observer h,
      anonymity G leader h u = candidate h u) ∧
    (agents G leader h (CoreTiming.levelsAt G leader (2 * m - 2) observer h)).card = m ∧
    agents G leader (m - 1) (CoreTiming.levelsAt G leader (2 * m - 2) observer (m - 1)) =
      agents G leader h (CoreTiming.levelsAt G leader (2 * m - 2) observer h) := by
  classical
  let visible := CoreTiming.levelsAt G leader (2 * m - 2) observer
  have wrong : m ≠ Fintype.card V := Nat.ne_of_lt small
  have singleton := C.false_final_singleton wrong connected
  have anchorEq := C.false_anchor_actual_eq_descendants wrong connected
  have maps := CoreHistory.ancestor_visible_of_parent_visible G leader h (m - 1)
    C.anchor_le_final visible C.all_parent_visible
  have hcount : (visible (m - 1)).card = ∑ u ∈ visible h, (C.descendants u).card :=
    Finset.card_eq_sum_card_fiberwise maps
  have anchorMass : (∑ u ∈ visible h, anonymity G leader h u) = (visible (m - 1)).card := by
    rw [hcount]
    exact Finset.sum_congr rfl anchorEq
  have finalMass : (∑ i ∈ visible (m - 1), anonymity G leader (m - 1) i) = (visible (m - 1)).card := by
    calc
      _ = ∑ _ ∈ visible (m - 1), 1 := Finset.sum_congr rfl singleton
      _ = _ := by simp
  have smallEach : ∀ u ∈ visible h, anonymity G leader h u ≤ candidate h u := by
    intro u hu
    rw [anchorEq u hu]
    exact C.suffix_audit u hu
  have finalBound : (visible (m - 1)).card ≤ m := by
    rw [← anchorMass, ← C.anchor_total]
    exact Finset.sum_le_sum smallEach
  have hexposure := tail_exposure G leader connected (m - 1) ((2 * m - 2) - (m - 1)) observer
  have hpos := C.anchor_positive
  have hfinal := C.anchor_le_final
  have htime : (2 * m - 2) - (m - 1) + 1 = m := by omega
  rw [htime, Nat.min_eq_right (Nat.le_of_lt small)] at hexposure
  change m ≤ ∑ i ∈ visible (m - 1), anonymity G leader (m - 1) i at hexposure
  rw [finalMass] at hexposure
  have countEq : (visible (m - 1)).card = m := Nat.le_antisymm finalBound hexposure
  have massEq : (∑ u ∈ visible h, anonymity G leader h u) = m := anchorMass.trans countEq
  refine ⟨total_credit_eq_forces_local_eq (visible h) (candidate h) (anonymity G leader h)
    smallEach (massEq.trans C.anchor_total.symm), ?_, ?_⟩
  · exact (agents_card G leader h _).trans massEq
  · apply Finset.eq_of_subset_of_card_le (agents_refine G leader h (m - 1) C.anchor_le_final visible C.all_parent_visible)
    rw [agents_card, agents_card, anchorMass, finalMass]

/-- The anchor of a hypothetical false short audit must be its final level. -/
theorem false_anchor_is_final (small : m < Fintype.card V)
    (connected : ∀ t, 0 < t → StronglyConnected (fun u v => 0 < G t u v)) : h = m - 1 := by
  classical
  obtain ⟨_, hcard, heq⟩ := C.false_anchor_rigidity small connected
  have hle := C.anchor_le_final
  by_contra hne
  have hlt : h < m - 1 := lt_of_le_of_ne hle hne
  let visible := CoreTiming.levelsAt G leader (2 * m - 2) observer
  have subset1 := agents_refine G leader h (h + 1) (by omega) visible
    (fun r hr => C.all_parent_visible r (by omega))
  have subset2 := agents_refine G leader (h + 1) (m - 1) (by omega) visible C.all_parent_visible
  have same : agents G leader (h + 1) (visible (h + 1)) = agents G leader h (visible h) := by
    apply Finset.Subset.antisymm subset1
    rw [← heq]
    exact subset2
  have proper : agents G leader h (visible h) ≠ Finset.univ := by
    intro hall
    have := congrArg Finset.card hall
    rw [hcard, Finset.card_univ] at this
    omega
  exact agents_strict_refinement G leader (2 * m - 2) h (by omega) observer
    (connected (h + 1) (by omega)) proper same

end Checks
end Counting.ShortAudit
