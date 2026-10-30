import Counting.HardnessAlternativeNonleaders
import Counting.RealizabilityRecognition

namespace Counting.HardnessReduction
open Counting.HardnessPath Counting.Realizability

variable {q m : Nat} (inst : X3C.Instance q m)

theorem baseline_observer_realizable (large : 2 ≤ q) (a : Agent (X3C.baselineGroups q m)) :
    Realizable 1 (X3C.baselineMass q m+1)
      (history (HardnessBaseline.X3CBaseline.graph inst) (leader (X3C.baselineGroups q m)) (X3C.base q) a) :=
  ⟨Agent (X3C.baselineGroups q m), inferInstance, HardnessBaseline.X3CBaseline.graph inst,
    leader (X3C.baselineGroups q m), a, HardnessBaseline.X3CBaseline.order,
    HardnessBaseline.X3CBaseline.admissible inst large, rfl⟩

/-- Exact covers supply an alternate order for every baseline observer.
Leader and nonleaders may use different alternate final-round graphs. -/
theorem alternate_observer_realizable (large : 2 ≤ q) (chosen : Finset (Fin m))
    (cover : inst.IsExactCover chosen) (a : Agent (X3C.baselineGroups q m)) :
    Realizable 1 (X3C.baselineMass q m+q)
      (history (HardnessBaseline.X3CBaseline.graph inst) (leader (X3C.baselineGroups q m)) (X3C.base q) a) := by
  cases a with
  | none => exact HardnessAlternative.X3CAlternative.realizes inst chosen large cover
  | some a => exact HardnessAlternative.X3CAlternative.nonleaders_realizable inst chosen large cover a

theorem cover_observer_not_unique (large : 2 ≤ q) (chosen : Finset (Fin m))
    (cover : inst.IsExactCover chosen) (a : Agent (X3C.baselineGroups q m)) :
    ¬ AtMostOneVista 1
      (history (HardnessBaseline.X3CBaseline.graph inst) (leader (X3C.baselineGroups q m)) (X3C.base q) a) := by
  intro unique
  have equal := unique (baseline_observer_realizable inst large a)
    (alternate_observer_realizable inst large chosen cover a)
  omega

theorem cover_not_atMostOne (large : 2 ≤ q) (chosen : Finset (Fin m))
    (cover : inst.IsExactCover chosen) :
    ¬ AtMostOneVista 1 (HardnessBaseline.X3CBaseline.leaderView inst) :=
  cover_observer_not_unique inst large chosen cover none

/-- The complement-X3C reduction's forward implication for the explicit
network problem, with admissibility already proved by the baseline graph. -/
theorem cover_not_someAgentKnows (large : 2 ≤ q) (chosen : Finset (Fin m))
    (cover : inst.IsExactCover chosen) :
    ¬ SomeAgentKnows 1 (HardnessBaseline.X3CBaseline.graph inst)
      (leader (X3C.baselineGroups q m)) (X3C.base q) := by
  rintro ⟨_, a, unique⟩
  exact cover_observer_not_unique inst large chosen cover a unique

theorem cover_orders_in_spectrum (large : 2 ≤ q) (chosen : Finset (Fin m))
    (cover : inst.IsExactCover chosen) :
    {X3C.baselineMass q m+1, X3C.baselineMass q m+q} ⊆
      spectrum 1 (HardnessBaseline.X3CBaseline.leaderView inst) := by
  intro N member
  rcases Set.mem_insert_iff.mp member with equal | last
  · exact equal ▸ baseline_observer_realizable inst large none
  · have equal := Set.mem_singleton_iff.mp last
    exact equal ▸ alternate_observer_realizable inst large chosen cover none

end Counting.HardnessReduction
