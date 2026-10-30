import Counting.HardnessReductionForward
import Counting.HardnessVisibleConverse

/-! Exact semantic reductions for both recognition problems. These theorems
quantify over every finite admissible realization of the produced vista.
Polynomial encoding size, machine running time and the NP-completeness of
the source problem are separate proof obligations. -/
namespace Counting.HardnessReduction
open Counting.HardnessPath Counting.Realizability
open scoped Classical

variable {q m : Nat} (inst : X3C.Instance q m)

/-- Every compatible order is the baseline order, or the cover order with
an exact-cover witness. Both alternatives have explicit admissible networks. -/
theorem spectrum_member_iff (large : 2 ≤ q) (N : Nat) :
    N ∈ spectrum 1 (HardnessBaseline.X3CBaseline.leaderView inst) ↔
      N = X3C.baselineMass q m+1 ∨
        (N = X3C.baselineMass q m+q ∧ ∃ chosen, inst.IsExactCover chosen) := by
  constructor
  · exact HardnessVisible.realization_dichotomy inst large N
  · rintro (rfl | ⟨rfl, chosen, cover⟩)
    · exact baseline_observer_realizable inst large none
    · exact alternate_observer_realizable inst large chosen cover none

/-- The complete order spectrum in the paper: a singleton when there is no
exact cover, and exactly the two distinct orders R+1 and R+q otherwise. -/
theorem spectrum_exact (large : 2 ≤ q) :
    spectrum 1 (HardnessBaseline.X3CBaseline.leaderView inst) =
      if ∃ chosen, inst.IsExactCover chosen then
        {X3C.baselineMass q m+1, X3C.baselineMass q m+q}
      else {X3C.baselineMass q m+1} := by
  ext N
  rw [spectrum_member_iff inst large N]
  by_cases cover : ∃ chosen, inst.IsExactCover chosen
  · simp [cover]
  · simp [cover]

theorem spectrum_no_cover (large : 2 ≤ q) (noCover : ¬ ∃ chosen, inst.IsExactCover chosen) :
    spectrum 1 (HardnessBaseline.X3CBaseline.leaderView inst) = {X3C.baselineMass q m+1} := by
  rw [spectrum_exact inst large, if_neg noCover]

theorem spectrum_has_cover (large : 2 ≤ q) (cover : ∃ chosen, inst.IsExactCover chosen) :
    spectrum 1 (HardnessBaseline.X3CBaseline.leaderView inst) =
      {X3C.baselineMass q m+1, X3C.baselineMass q m+q} := by
  rw [spectrum_exact inst large, if_pos cover]

/-- Complement-X3C is equivalent to uniqueness of the produced leader vista.
The bound q≥2 ensures the cover order differs from the baseline order. -/
theorem atMostOneVista_iff_noExactCover (large : 2 ≤ q) :
    AtMostOneVista 1 (HardnessBaseline.X3CBaseline.leaderView inst) ↔
      ¬ ∃ chosen, inst.IsExactCover chosen := by
  constructor
  · rintro unique ⟨chosen, cover⟩
    exact cover_not_atMostOne inst large chosen cover unique
  · intro noCover N first M second
    have firstOrder := (spectrum_member_iff inst large N).mp first
    have secondOrder := (spectrum_member_iff inst large M).mp second
    have only (K : Nat) (possible : K = X3C.baselineMass q m+1 ∨
        (K = X3C.baselineMass q m+q ∧ ∃ chosen, inst.IsExactCover chosen)) :
        K = X3C.baselineMass q m+1 :=
      possible.elim id (fun alternate => (noCover alternate.2).elim)
    exact (only N firstOrder).trans (only M secondOrder).symm

/-- Complement-X3C is also equivalent to the explicit network having an
agent who knows its order. Without a cover the leader knows; with a cover,
the two final-round constructions provide ambiguity for every observer. -/
theorem someAgentKnows_iff_noExactCover (large : 2 ≤ q) :
    SomeAgentKnows 1 (HardnessBaseline.X3CBaseline.graph inst)
      (leader (X3C.baselineGroups q m)) (X3C.base q) ↔
        ¬ ∃ chosen, inst.IsExactCover chosen := by
  constructor
  · rintro known ⟨chosen, cover⟩
    exact cover_not_someAgentKnows inst large chosen cover known
  · intro noCover
    exact ⟨HardnessBaseline.X3CBaseline.admissible inst large, none,
      (atMostOneVista_iff_noExactCover inst large).mpr noCover⟩

/-- The two semantic target problems agree on the constructed instances. -/
theorem recognition_problems_agree (large : 2 ≤ q) :
    AtMostOneVista 1 (HardnessBaseline.X3CBaseline.leaderView inst) ↔
      SomeAgentKnows 1 (HardnessBaseline.X3CBaseline.graph inst)
        (leader (X3C.baselineGroups q m)) (X3C.base q) :=
  (atMostOneVista_iff_noExactCover inst large).trans
    (someAgentKnows_iff_noExactCover inst large).symm

end Counting.HardnessReduction
