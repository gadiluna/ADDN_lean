import Counting.HardnessAlternativeLeader

namespace Counting.HardnessAlternative
open Counting.HardnessPath DirectedCounting

variable {I : Type} [Fintype I]

/-- An ordinary final star reproduces every baseline nonleader's history
at a member of the same old class in a differently sized population. -/
theorem ordinary_star_member_matches (coeff left right : I → Nat) (C r : Nat)
    (leftWeight : (∑ i, coeff i * left i) = C)
    (rightWeight : (∑ i, coeff i * right i) = C)
    (leftLength : ∀ i, r < left i) (rightLength : ∀ i, r < right i)
    (a : Member left) : ∃ b : Member right,
    history (HardnessBaseline.network coeff left (r+1)) (leader left) (r+1) (some a) =
      history (HardnessBaseline.network coeff right (r+1)) (leader right) (r+1) (some b) := by
  obtain ⟨i, p⟩ := a
  let position : Fin (right i) := ⟨min p.val r, (min_le_right _ _).trans_lt (rightLength i)⟩
  refine ⟨⟨i, position⟩, ?_⟩
  have old : history (pathNetwork coeff left) (leader left) r (some ⟨i, p⟩) =
      history (pathNetwork coeff right) (leader right) r (some ⟨i, position⟩) :=
    common_member_history coeff left right C r leftWeight rightWeight leftLength rightLength i p position
      (by dsimp [position]; simp only [min_assoc, min_self])
  have priorLeft : history (HardnessBaseline.network coeff left (r+1)) (leader left) r =
      history (pathNetwork coeff left) (leader left) r :=
    funext (HardnessBaseline.prefix_history _ _ _ _ (by omega))
  have priorRight : history (HardnessBaseline.network coeff right (r+1)) (leader right) r =
      history (pathNetwork coeff right) (leader right) r :=
    funext (HardnessBaseline.prefix_history _ _ _ _ (by omega))
  have finalLeft := HardnessBaseline.network_after coeff left (r+1) (r+1) (le_refl _)
  have finalRight := HardnessBaseline.network_after coeff right (r+1) (r+1) (le_refl _)
  simp only [history, finalLeft, finalRight, priorLeft, priorRight]
  refine Prod.ext old (Prod.ext ?_ ?_)
  · rw [star_member_outdegree, star_member_outdegree]
  · rw [star_incoming_member, star_incoming_member]
    exact congrArg (Multiset.replicate (coeff i))
      (common_leader_history coeff left right C r leftWeight rightWeight leftLength rightLength)

namespace X3CAlternative
variable {q m : Nat} (inst : X3C.Instance q m) (chosen : Finset (Fin m))

noncomputable def ordinaryGraph : Nat → Agent (X3C.coverGroups q m chosen) → Agent (X3C.coverGroups q m chosen) → Nat :=
  HardnessBaseline.network inst.coefficient (X3C.coverGroups q m chosen) (X3C.base q)

theorem nonleader_history_eq (cover : inst.IsExactCover chosen)
    (a : Member (X3C.baselineGroups q m)) : ∃ b : Member (X3C.coverGroups q m chosen),
    history (HardnessBaseline.X3CBaseline.graph inst) (leader (X3C.baselineGroups q m))
      (X3C.base q) (some a) =
    history (ordinaryGraph inst chosen) (leader (X3C.coverGroups q m chosen))
      (X3C.base q) (some b) := by
  have positive : 0 < X3C.base q := by unfold X3C.base; omega
  have round : X3C.base q-1+1 = X3C.base q := by omega
  have common := ordinary_star_member_matches inst.coefficient (X3C.baselineGroups q m)
    (X3C.coverGroups q m chosen) inst.weightedTarget (X3C.base q-1)
    inst.baselineGroups_equation (inst.coverGroups_equation chosen cover)
    (by
      intro i
      have low : X3C.base q ≤ X3C.baselineGroups q m i := by cases i <;> simp [X3C.baselineGroups]
      omega)
    (by
      intro i
      have low : X3C.base q ≤ X3C.coverGroups q m chosen i := by cases i <;> simp [X3C.coverGroups]
      omega) a
  rw [round] at common
  exact common

/-- One ordinary-star alternate network supplies compatible histories for
every baseline nonleader; the matching agent may depend on the old class. -/
theorem nonleaders_realizable (large : 2 ≤ q) (cover : inst.IsExactCover chosen)
    (a : Member (X3C.baselineGroups q m)) :
    Realizability.Realizable 1 (X3C.baselineMass q m+q)
      (history (HardnessBaseline.X3CBaseline.graph inst) (leader (X3C.baselineGroups q m))
        (X3C.base q) (some a)) := by
  obtain ⟨b, matching⟩ := nonleader_history_eq inst chosen cover a
  refine ⟨Agent (X3C.coverGroups q m chosen), inferInstance, ordinaryGraph inst chosen,
    leader (X3C.coverGroups q m chosen), some b, ?_, ?_, matching.symm⟩
  · exact (population _).trans (inst.coverGroups_order chosen cover)
  · exact HardnessBaseline.network_admissible _ _ _ (inst.coefficient_positive large)

end X3CAlternative
end Counting.HardnessAlternative
