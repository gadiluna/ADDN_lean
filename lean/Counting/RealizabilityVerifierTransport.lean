import Counting.RealizabilityVerifier

namespace Counting.RealizabilityVerifier
open Counting.Executable Counting.TimingProtocolLocal
open scoped BigOperators

theorem levelIndex_present (vista : Vista) (r : ℕ) (i : LevelIndex vista r) :
    i.val.val ∈ levelNodes vista r :=
  (mem_levelNodes _ _ _).mpr ⟨i.val.isLt, i.property⟩

theorem bottom_inside (vista : Vista) (valid : vista.valid = true) : vista.bottom < vista.nodes.size := by
  simp only [Vista.valid, Bool.and_eq_true, decide_eq_true_eq] at valid
  exact valid.1.1.1

theorem stored_level_le (vista : Vista) (valid : vista.valid = true) (i : Fin vista.nodes.size) :
    (vista.node i.val).level ≤ (vista.node vista.bottom).level := by
  have seen := stored_history_visible vista valid i.val i.isLt
  by_contra no
  rw [levels_above _ _ _ (by omega)] at seen
  exact Finset.notMem_empty _ seen

noncomputable def levelDecode (vista : Vista) (valid : vista.valid = true) (r : ℕ)
    (i : LevelIndex vista r) :
    Realizability.VisibleNode (levels (vista.node vista.bottom).level vista.denotes) r :=
  ⟨decodeNode vista r i.val.val, by
    rw [← decodedLevel_eq_levels vista valid]
    exact (mem_decodedLevel _ _ _).mpr ⟨i.val.val, i.val.isLt, i.property, rfl⟩⟩

theorem levelDecode_bijective (vista : Vista) (valid : vista.valid = true) (r : ℕ) :
    Function.Bijective (levelDecode vista valid r) := by
  constructor
  · intro i j same
    apply Subtype.ext
    apply Fin.ext
    exact decodeNode_injective vista valid r i.val.val j.val.val i.val.isLt j.val.isLt
      i.property j.property (congrArg Subtype.val same)
  · intro H
    rcases H with ⟨H, visible⟩
    rw [← decodedLevel_eq_levels vista valid] at visible
    obtain ⟨i, inside, level, same⟩ := (mem_decodedLevel _ _ _).mp visible
    exact ⟨⟨⟨i, inside⟩, level⟩, Subtype.ext same⟩

noncomputable def levelEquiv (vista : Vista) (valid : vista.valid = true) (r : ℕ) :
    LevelIndex vista r ≃ Realizability.VisibleNode (levels (vista.node vista.bottom).level vista.denotes) r :=
  Equiv.ofBijective (levelDecode vista valid r) (levelDecode_bijective vista valid r)

@[simp] theorem levelEquiv_val (vista : Vista) (valid : vista.valid = true) (r : ℕ)
    (i : LevelIndex vista r) :
    (levelEquiv vista valid r i).val = decodeNode vista r i.val.val := rfl

theorem childCount_decode (vista : Vista) (valid : vista.valid = true) (weights : Array ℕ)
    (r : ℕ) (old : LevelIndex vista r) :
    Realizability.childCount (levels (vista.node vista.bottom).level vista.denotes)
      (decodedWeight vista weights) r (decodeNode vista r old.val.val) =
      childCount vista weights r old.val.val := by
  unfold Realizability.childCount Realizability.children
  rw [← decodedLevel_eq_levels vista valid]
  exact sum_decoded_children vista valid weights r old.val.val (levelIndex_present vista r old)

theorem leaving_decode (vista : Vista) (valid : vista.valid = true) (weights : Array ℕ)
    (r : ℕ) (old : LevelIndex vista r) :
    Realizability.leaving (levels (vista.node vista.bottom).level vista.denotes)
      (decodedWeight vista weights) r (decodeNode vista r old.val.val) =
      leaving vista weights r old.val.val := by
  unfold Realizability.leaving leaving
  rw [childCount_decode vista valid weights r old,
    decodedWeight_decode vista valid weights r old.val.val (levelIndex_present vista r old)]
  rfl

theorem supply_decode (vista : Vista) (valid : vista.valid = true) (weights : Array ℕ)
    (r : ℕ) (old : LevelIndex vista r) :
    Realizability.supply (levels (vista.node vista.bottom).level vista.denotes)
      (decodedWeight vista weights) r (decodeNode vista r old.val.val) =
      supply vista weights r old.val.val := by
  classical
  unfold Realizability.supply Realizability.children supply
  rw [← decodedLevel_eq_levels vista valid, sum_filter_decodedLevel vista valid,
    decoded_children_filter vista valid r old.val.val (levelIndex_present vista r old)]
  apply congrArg List.sum
  apply List.map_congr_left
  intro i hi
  rw [degree_decode, decodedWeight_decode vista valid weights (r + 1) i (List.mem_filter.mp hi).1]
  rfl

theorem demand_decode (vista : Vista) (valid : vista.valid = true) (weights : Array ℕ)
    (r : ℕ) (old : LevelIndex vista r) :
    Realizability.demand (levels (vista.node vista.bottom).level vista.denotes)
      (decodedWeight vista weights) r (decodeNode vista r old.val.val) =
      demand vista weights r old.val.val := by
  classical
  unfold Realizability.demand demand
  rw [← decodedLevel_eq_levels vista valid, sum_decodedLevel vista valid]
  apply congrArg List.sum
  apply List.map_congr_left
  intro i hi
  have data := (mem_levelNodes vista (r + 1) i).mp hi
  rw [red_decode vista valid r old.val.val i old.val.isLt data.1 old.property data.2,
    decodedWeight_decode vista valid weights (r + 1) i hi]
  rfl

theorem hidden_decode (N : ℕ) (vista : Vista) (valid : vista.valid = true) (weights : Array ℕ)
    (r : ℕ) :
    Realizability.hidden N (levels (vista.node vista.bottom).level vista.denotes)
      (decodedWeight vista weights) r = hidden N vista weights r := by
  classical
  unfold Realizability.hidden hidden
  rw [← decodedLevel_eq_levels vista valid, sum_decodedLevel vista valid]
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  exact fun i hi => decodedWeight_decode vista valid weights (r + 1) i hi

theorem initialCount_decode (vista : Vista) (valid : vista.valid = true) (weights : Array ℕ) (b : Bool) :
    Realizability.initialCount (levels (vista.node vista.bottom).level vista.denotes)
      (decodedWeight vista weights) b = initialCount vista weights b := by
  classical
  have sumForm : Realizability.initialCount (levels (vista.node vista.bottom).level vista.denotes)
      (decodedWeight vista weights) b =
      ∑ H ∈ levels (vista.node vista.bottom).level vista.denotes 0,
        if H = b then decodedWeight vista weights 0 H else 0 := by
    simp only [Realizability.initialCount, Finset.sum_ite_eq']
    rfl
  rw [sumForm, ← decodedLevel_eq_levels vista valid, sum_decodedLevel vista valid]
  unfold initialCount
  apply congrArg List.sum
  apply List.map_congr_left
  intro i hi
  rw [decodedWeight_decode vista valid weights 0 i hi]
  simp only [decodeNode, weight]
  split_ifs <;> first | rfl | contradiction

noncomputable def roundEquiv (N : ℕ) (vista : Vista) (valid : vista.valid = true)
    (weights : Array ℕ) (r : ℕ) :
    RoundVertex N vista weights r ≃ Realizability.RoundVertex N
      (levels (vista.node vista.bottom).level vista.denotes) (decodedWeight vista weights) r :=
  Equiv.sumCongr (levelEquiv vista valid (r + 1))
    (Equiv.sumCongr (levelEquiv vista valid r) (finCongr (by
      unfold outsideSize Realizability.outsideSize
      rw [hidden_decode N vista valid weights r])))

theorem roundArc_decode (N : ℕ) (vista : Vista) (valid : vista.valid = true)
    (weights : Array ℕ) (r : ℕ) (x y : RoundVertex N vista weights r) :
    roundArc N vista weights r x y = true ↔
      Realizability.roundArc N (levels (vista.node vista.bottom).level vista.denotes)
        (decodedWeight vista weights) r
          (roundEquiv N vista valid weights r x) (roundEquiv N vista valid weights r y) := by
  rcases x with v | u | j <;> rcases y with w | z | i
  all_goals simp only [roundEquiv, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr,
    Realizability.roundArc, roundArc, levelEquiv_val, Bool.and_eq_true, Bool.or_eq_true,
    beq_iff_eq, decide_eq_true_eq, Bool.false_eq_true]
  · rw [parent_decode_eq_iff vista valid r z.val.val v.val.val
      (levelIndex_present vista r z) (levelIndex_present vista (r + 1) v), degree_decode]
  · rw [red_decode vista valid r u.val.val w.val.val u.val.isLt w.val.isLt u.property w.property]
  · rw [leaving_decode vista valid weights r u, demand_decode vista valid weights r u,
      supply_decode vista valid weights r u]
  · rw [leaving_decode vista valid weights r z]

theorem connected_decode (N : ℕ) (vista : Vista) (valid : vista.valid = true)
    (weights : Array ℕ) (r : ℕ) :
    DirectedCounting.StronglyConnected (fun x y => roundArc N vista weights r x y = true) ↔
    DirectedCounting.StronglyConnected (Realizability.roundArc N
      (levels (vista.node vista.bottom).level vista.denotes) (decodedWeight vista weights) r) :=
  connected_equiv (roundEquiv N vista valid weights r) _ _ (roundArc_decode N vista valid weights r)

end Counting.RealizabilityVerifier
