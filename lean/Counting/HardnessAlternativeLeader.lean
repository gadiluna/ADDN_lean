import Counting.HardnessAlternativeMessages
import Counting.HardnessBaseline
import Counting.RealizabilityComplete

namespace Counting.HardnessAlternative
open Counting.HardnessPath DirectedCounting
open scoped Classical

variable {I : Type} [Fintype I]

noncomputable def network (coeff size : I → Nat) (zero : I) (r : Nat) :
    Nat → Agent size → Agent size → Nat :=
  fun round => if round < r+1 then HardnessPath.edge coeff size else edge coeff size zero r

theorem network_admissible (coeff size : I → Nat) (zero : I) (r : Nat)
    (positive : ∀ i, 0 < coeff i) : Admissible 1 (network coeff size zero r) (leader size) := by
  refine ⟨by omega, leaders size, ?_⟩
  intro round _
  unfold network
  split
  · exact path_connected coeff size positive
  · exact connected coeff size zero r positive

omit [Fintype I] in
theorem network_loopless (coeff size : I → Nat) (zero : I) (r round : Nat) (a : Agent size) :
    network coeff size zero r round a a = 0 := by
  unfold network
  split
  · exact path_loopless coeff size a
  · exact loopless coeff size zero r a

theorem prefix_history (coeff size : I → Nat) (zero : I) (r t : Nat) (before : t ≤ r) (a : Agent size) :
    history (network coeff size zero r) (leader size) t a =
      history (pathNetwork coeff size) (leader size) t a := by
  induction t generalizing a with
  | zero => rfl
  | succ t ih =>
      have previous : history (network coeff size zero r) (leader size) t =
          history (pathNetwork coeff size) (leader size) t := funext (ih (by omega))
      have round : network coeff size zero r (t+1) = HardnessPath.edge coeff size := if_pos (by omega)
      simp only [history, round, previous, pathNetwork]

theorem baseline_receipts (coeff size : I → Nat) (C r : Nat) (zero : I)
    (zeroSize : size zero = r+2) (otherSizes : ∀ i, i ≠ zero → size i = r+1)
    (weighted : (∑ i, coeff i * size i) = C) (lengths : ∀ i, r < size i) :
    incoming (star coeff size) (history (pathNetwork coeff size) (leader size) r) none =
      ∑ i : I, ((∑ p : Fin r, ({memberHistory coeff C r i p.val} : Multiset (FullHistory r))) +
        Multiset.replicate (if i = zero then 2 else 1) (memberHistory coeff C r i r)) := by
  rw [star_canonical_receipts coeff size C r weighted lengths]
  apply Finset.sum_congr rfl
  intro i _
  congr 2
  by_cases equal : i = zero
  · subst i
    simp [zeroSize]
  · simp [otherSizes i equal, equal]

/-- The modified final round duplicates only the old group-zero suffix
state and hides one old suffix copy in every selected group via a relay. -/
theorem leader_matches (coeff left right : I → Nat) (C r : Nat) (zero : I)
    (leftZero : left zero = r+2) (leftOther : ∀ i, i ≠ zero → left i = r+1)
    (rightZero : right zero = r+1)
    (rightOther : ∀ i, i ≠ zero → right i = r+1 ∨ right i = r+2)
    (leftWeight : (∑ i, coeff i * left i) = C)
    (rightWeight : (∑ i, coeff i * right i) = C)
    (leftLength : ∀ i, r < left i) (rightLength : ∀ i, r < right i) :
    history (network coeff right zero r) (leader right) (r+1) none =
      history (HardnessBaseline.network coeff left (r+1)) (leader left) (r+1) none := by
  have priorRight : history (network coeff right zero r) (leader right) r =
      history (pathNetwork coeff right) (leader right) r := funext (prefix_history _ _ _ _ _ (le_refl _))
  have priorLeft : history (HardnessBaseline.network coeff left (r+1)) (leader left) r =
      history (pathNetwork coeff left) (leader left) r :=
    funext (HardnessBaseline.prefix_history _ _ _ _ (by omega))
  have finalRight : network coeff right zero r (r+1) = edge coeff right zero r :=
    if_neg (Nat.lt_irrefl _)
  have finalLeft : HardnessBaseline.network coeff left (r+1) (r+1) = star coeff left :=
    HardnessBaseline.network_after _ _ _ _ (le_refl _)
  simp only [history, finalRight, finalLeft, priorRight, priorLeft]
  refine Prod.ext (common_leader_history coeff right left C r rightWeight leftWeight rightLength leftLength)
    (Prod.ext ?_ ?_)
  · exact (leader_outdegree coeff right zero r).trans (rightWeight.trans
      (leftWeight.symm.trans (star_leader_outdegree coeff left).symm))
  · rw [canonical_leader_receipts coeff right C r zero rightZero rightOther rightWeight rightLength,
      baseline_receipts coeff left C r zero leftZero leftOther leftWeight leftLength]

namespace X3CAlternative
variable {q m : Nat} (inst : X3C.Instance q m) (chosen : Finset (Fin m))

noncomputable def graph : Nat → Agent (X3C.coverGroups q m chosen) → Agent (X3C.coverGroups q m chosen) → Nat :=
  network inst.coefficient (X3C.coverGroups q m chosen) none (X3C.base q-1)

theorem leader_history_eq (cover : inst.IsExactCover chosen) :
    history (graph inst chosen) (leader (X3C.coverGroups q m chosen)) (X3C.base q) none =
      HardnessBaseline.X3CBaseline.leaderView inst := by
  have basePositive : 0 < X3C.base q := by unfold X3C.base; omega
  have round : X3C.base q-1+1 = X3C.base q := by omega
  have common := leader_matches inst.coefficient (X3C.baselineGroups q m) (X3C.coverGroups q m chosen)
    inst.weightedTarget (X3C.base q-1) none
    (by simp only [X3C.baselineGroups]; omega)
    (by intro i different; cases i with
        | none => exact (different rfl).elim
        | some j => simpa only [X3C.baselineGroups] using round.symm)
    (by simpa only [X3C.coverGroups] using round.symm)
    (by intro i different; cases i with
        | none => exact (different rfl).elim
        | some j => by_cases member : j ∈ chosen <;> simp [X3C.coverGroups, member, round])
    inst.baselineGroups_equation (inst.coverGroups_equation chosen cover)
    (by intro i; cases i <;> simp [X3C.baselineGroups]; omega)
    (by
      intro i
      have low : X3C.base q ≤ X3C.coverGroups q m chosen i := by cases i <;> simp [X3C.coverGroups]
      omega)
  rw [round] at common
  simpa only [graph, HardnessBaseline.X3CBaseline.leaderView,
    HardnessBaseline.X3CBaseline.graph] using common

theorem realizes (large : 2 ≤ q) (cover : inst.IsExactCover chosen) :
    Realizability.Realizable 1 (X3C.baselineMass q m+q)
      (HardnessBaseline.X3CBaseline.leaderView inst) := by
  refine ⟨Agent (X3C.coverGroups q m chosen), inferInstance, graph inst chosen,
    leader (X3C.coverGroups q m chosen), none, ?_, ?_, leader_history_eq inst chosen cover⟩
  · exact (population _).trans (inst.coverGroups_order chosen cover)
  · exact network_admissible _ _ _ _ (inst.coefficient_positive large)

end X3CAlternative
end Counting.HardnessAlternative
