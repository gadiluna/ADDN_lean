import Counting.HardnessBaseline
import Counting.HardnessExhaustive

namespace Counting.HardnessVisible
open DirectedCounting PaperHistory TimingProtocolLocal HardnessPath HardnessBaseline

variable {V : Type} [Fintype V]
variable (G : Nat → V → V → Nat) (leader : V → Bool)

/-- Full represented fibers can equivalently be selected by their intrinsic
history labels, without using any anonymity from the baseline realization. -/
theorem mem_represented_iff (t : Nat) (observer : V) (r : Nat) (within : r ≤ t) (v : V) :
    v ∈ HardnessExhaustive.represented G leader t observer r ↔
      history G leader r v ∈ levels t (history G leader t observer) r := by
  classical
  rw [HardnessExhaustive.mem_represented, levels_eq_image G leader t r within observer]
  constructor
  · intro member
    exact Finset.mem_image.mpr ⟨_, member, nodeHistory_classOf G leader r v⟩
  · rintro member
    obtain ⟨node, visible, equal⟩ := Finset.mem_image.mp member
    have eq := (nodeHistory_injective G leader r) (equal.trans (nodeHistory_classOf G leader r v).symm)
    exact eq ▸ visible

theorem represented_histories (t : Nat) (observer : V) (r : Nat) (within : r ≤ t) :
    (HardnessExhaustive.represented G leader t observer r).image (history G leader r) =
      levels t (history G leader t observer) r := by
  classical
  apply Finset.ext
  intro H
  constructor
  · rintro member
    obtain ⟨v, represented, rfl⟩ := Finset.mem_image.mp member
    exact (mem_represented_iff G leader t observer r within v).mp represented
  · intro member
    rw [levels_eq_image G leader t r within observer] at member
    obtain ⟨node, visible, rfl⟩ := Finset.mem_image.mp member
    refine Finset.mem_image.mpr ⟨node.out, ?_, rfl⟩
    apply (HardnessExhaustive.mem_represented G leader t observer r node.out).mpr
    simpa only [classOf_out] using visible

theorem visible_card_le_represented (t : Nat) (observer : V) (r : Nat) (within : r ≤ t) :
    (levels t (history G leader t observer) r).card ≤
      (HardnessExhaustive.represented G leader t observer r).card := by
  rw [← represented_histories G leader t observer r within]
  exact Finset.card_image_le

theorem ancestor_history (r t : Nat) (within : r ≤ t) (v : V) :
    ancestor r t (history G leader t v) = history G leader r v := by
  unfold ancestor
  rw [dif_pos within, cast_history G leader t (r+(t-r)) (Nat.add_sub_of_le within).symm v,
    blackAncestor_history]

variable {q m : Nat} (inst : X3C.Instance q m)

/-- Baseline node labels expressed only by group and exposed position.
The finite representative set includes the single suffix representative r. -/
theorem baseline_level_mem_iff (r : Nat) (before : r < X3C.base q) (H : FullHistory r) :
    H ∈ levels (X3C.base q) (X3CBaseline.leaderView inst) r ↔
      H = leaderHistory inst.coefficient inst.weightedTarget r ∨
      ∃ (i : Option (Fin m)) (p : Fin (r+1)),
        H = memberHistory inst.coefficient inst.weightedTarget r i p.val := by
  classical
  rw [X3CBaseline.intrinsic_visible_prefix inst r before]
  have lengths : ∀ i, r < X3C.baselineGroups q m i := fun i =>
    before.trans_le (X3CBaseline.baseline_lengths i)
  have physical := path_histories inst.coefficient (X3C.baselineGroups q m)
    inst.weightedTarget inst.baselineGroups_equation r lengths
  constructor
  · intro member
    obtain ⟨node, _, rfl⟩ := Finset.mem_image.mp member
    unfold nodeHistory
    have prefixEq : history (X3CBaseline.graph inst) (HardnessPath.leader (X3C.baselineGroups q m)) r node.out =
        history (pathNetwork inst.coefficient (X3C.baselineGroups q m)) (HardnessPath.leader (X3C.baselineGroups q m)) r node.out :=
      prefix_history _ _ _ r before node.out
    rw [prefixEq]
    cases agent : node.out with
    | none => exact Or.inl physical.1
    | some a =>
      obtain ⟨i, p⟩ := a
      refine Or.inr ⟨i, ⟨min p.val r, by omega⟩, ?_⟩
      rw [physical.2]
      exact (member_eq_iff_min _ _ _ _ _ _).mpr (by simp only [min_assoc, min_self])
  · rintro (rfl | ⟨i, p, rfl⟩)
    · refine Finset.mem_image.mpr ⟨classOf _ _ r none, Finset.mem_univ _, ?_⟩
      rw [nodeHistory_classOf]
      exact (prefix_history _ _ _ r before none).trans physical.1
    · let position : Fin (X3C.baselineGroups q m i) := ⟨p.val, lt_of_le_of_lt (by omega) (lengths i)⟩
      refine Finset.mem_image.mpr ⟨classOf _ _ r (some ⟨i, position⟩), Finset.mem_univ _, ?_⟩
      rw [nodeHistory_classOf]
      exact (prefix_history _ _ _ r before _).trans (physical.2 i position)

/-- The final represented set has at least R agents in every realization,
even when none of its full fibers is a singleton. -/
theorem final_represented_lower (large : 2 ≤ q) (observer : V)
    (same : history G leader (X3C.base q) observer = X3CBaseline.leaderView inst) :
    X3C.baselineMass q m ≤
      (HardnessExhaustive.represented G leader (X3C.base q) observer (X3C.base q-1)).card := by
  have bound := visible_card_le_represented G leader (X3C.base q) observer (X3C.base q-1) (by omega)
  rw [same, X3CBaseline.intrinsic_final_card inst large] at bound
  exact bound

end Counting.HardnessVisible
