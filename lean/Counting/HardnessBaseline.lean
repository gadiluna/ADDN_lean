import Counting.HardnessBaselinePartition
import Counting.TimingProtocolLocal

namespace Counting.HardnessBaseline
open DirectedCounting PaperHistory HardnessPath

namespace X3CBaseline
variable {q m : Nat} (inst : X3C.Instance q m)

noncomputable def leaderView : FullHistory (X3C.base q) :=
  history (graph inst) (leader (X3C.baselineGroups q m)) (X3C.base q) none

theorem baseline_lengths (i : Option (Fin m)) : X3C.base q ≤ X3C.baselineGroups q m i := by
  cases i <;> simp [X3C.baselineGroups]

/-- Each coefficient group has precisely B=q+3 distinct visible classes at
level B−1; distinctness is supplied by the actual X3C coefficient encoding. -/
theorem final_group_nodes (large : 2 ≤ q) (i : Option (Fin m)) :
    (groupNodes inst.coefficient (X3C.baselineGroups q m) (X3C.base q) (X3C.base q-1) i).card =
      X3C.base q :=
  final_group_card _ _ (inst.coefficient_injective large) _ inst.weightedTarget
    (by unfold X3C.base; omega) inst.baselineGroups_equation baseline_lengths i

theorem final_level_nodes (large : 2 ≤ q) :
    Fintype.card (Node (graph inst) (leader (X3C.baselineGroups q m)) (X3C.base q-1)) =
      X3C.baselineMass q m := by
  have eq : X3C.base q-1+1 = X3C.base q := by unfold X3C.base; omega
  have count := prefix_node_card inst.coefficient (X3C.baselineGroups q m)
    (inst.coefficient_injective large) (X3C.base q) inst.weightedTarget (X3C.base q-1)
    inst.baselineGroups_equation (by unfold X3C.base; omega) (by unfold X3C.base; omega)
    (fun i => by have := baseline_lengths (q := q) (m := m) i; unfold X3C.base at *; omega)
  rw [eq] at count
  rw [← Nat.card_eq_fintype_card] at count ⊢
  simpa only [graph, Fintype.card_option, Fintype.card_fin, X3C.baselineMass] using count

/-- The leader sees all R preceding classes after the star, not merely one
representative from each physical group. -/
theorem final_visible_nodes (large : 2 ≤ q) :
    (CoreTiming.levelsAt (graph inst) (leader (X3C.baselineGroups q m))
      (X3C.base q) none (X3C.base q-1)).card = X3C.baselineMass q m := by
  rw [visible_prefix inst _ (by unfold X3C.base; omega), Finset.card_univ]
  exact final_level_nodes inst large

/-- Intrinsic full histories retain the same exhaustive prefix, so the
statement transports to any realization of this vista. -/
theorem intrinsic_visible_prefix (r : Nat) (before : r < X3C.base q) :
    TimingProtocolLocal.levels (X3C.base q) (leaderView inst) r =
      Finset.univ.image (TimingProtocolLocal.nodeHistory (graph inst)
        (leader (X3C.baselineGroups q m)) r) := by
  classical
  rw [leaderView, TimingProtocolLocal.levels_eq_image _ _ _ _ (by omega)]
  rw [visible_prefix inst r before]

theorem intrinsic_final_card (large : 2 ≤ q) :
    (TimingProtocolLocal.levels (X3C.base q) (leaderView inst) (X3C.base q-1)).card =
      X3C.baselineMass q m := by
  classical
  rw [intrinsic_visible_prefix inst _ (by unfold X3C.base; omega), Finset.card_image_iff.mpr]
  · rw [Finset.card_univ]
    exact final_level_nodes inst large
  · exact (TimingProtocolLocal.nodeHistory_injective (graph inst)
      (leader (X3C.baselineGroups q m)) (X3C.base q-1)).injOn

/-- The baseline required by the reduction is an admissible one-leader
network of order R+1, with the claimed exhaustive final prefix and B classes
per nonleader group. No arbitrary-realization cardinality bound is assumed. -/
theorem baseline_final_visible (large : 2 ≤ q) :
    Admissible 1 (graph inst) (leader (X3C.baselineGroups q m)) ∧
    Fintype.card (Agent (X3C.baselineGroups q m)) = X3C.baselineMass q m+1 ∧
    (∀ r, r < X3C.base q → CoreTiming.levelsAt (graph inst)
      (leader (X3C.baselineGroups q m)) (X3C.base q) none r = Finset.univ) ∧
    (∀ i, (groupNodes inst.coefficient (X3C.baselineGroups q m) (X3C.base q)
      (X3C.base q-1) i).card = X3C.base q) ∧
    (TimingProtocolLocal.levels (X3C.base q) (leaderView inst) (X3C.base q-1)).card =
      X3C.baselineMass q m :=
  ⟨admissible inst large, order, visible_prefix inst, final_group_nodes inst large,
    intrinsic_final_card inst large⟩

end X3CBaseline
end Counting.HardnessBaseline
