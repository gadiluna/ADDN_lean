import Counting.HardnessPathPrefix
import Counting.CoreTiming
import Counting.X3CShifted

namespace Counting.HardnessBaseline
open DirectedCounting PaperHistory HardnessPath

variable {I : Type} [Fintype I]

/-- The required path prefix followed by the ordinary star at B and forever
thereafter. The continuation is explicit and strongly connected. -/
noncomputable def network (coeff size : I → Nat) (B : Nat) : Nat → Agent size → Agent size → Nat :=
  fun round => if round < B then edge coeff size else star coeff size

omit [Fintype I] in
theorem network_before (coeff size : I → Nat) (B round : Nat) (before : round < B) :
    network coeff size B round = edge coeff size := if_pos before

omit [Fintype I] in
theorem network_after (coeff size : I → Nat) (B round : Nat) (after : B ≤ round) :
    network coeff size B round = star coeff size := if_neg (Nat.not_lt.mpr after)

omit [Fintype I] in
theorem network_loopless (coeff size : I → Nat) (B round : Nat) (a : Agent size) :
    network coeff size B round a a = 0 := by
  unfold network
  split
  · exact path_loopless coeff size a
  · exact star_loopless coeff size a

omit [Fintype I] in
theorem network_connected (coeff size : I → Nat) (B round : Nat) (positive : ∀ i, 0 < coeff i) :
    StronglyConnected (fun a b => 0 < network coeff size B round a b) := by
  unfold network
  split
  · exact path_connected coeff size positive
  · exact star_connected coeff size positive

theorem network_admissible (coeff size : I → Nat) (B : Nat) (positive : ∀ i, 0 < coeff i) :
    Admissible 1 (network coeff size B) (leader size) :=
  ⟨by omega, leaders size, fun round _ => network_connected coeff size B round positive⟩

theorem prefix_history (coeff size : I → Nat) (B r : Nat) (before : r < B) (a : Agent size) :
    history (network coeff size B) (leader size) r a =
      history (pathNetwork coeff size) (leader size) r a := by
  induction r generalizing a with
  | zero => rfl
  | succ r ih =>
      have previous : history (network coeff size B) (leader size) r =
          history (pathNetwork coeff size) (leader size) r := funext (ih (by omega))
      simp only [history, network_before coeff size B (r+1) before, previous, pathNetwork]

/-- The star exposes every previous physical history to its leader in one
round; the old leader's history is retained through the parent edge. -/
theorem star_exposes_support (coeff size : I → Nat)
    (G : Nat → Agent size → Agent size → Nat) (r : Nat)
    (starRound : G (r+1) = star coeff size) : causalSupport G r 1 none = Finset.univ := by
  classical
  apply Finset.eq_univ_of_forall
  intro a
  simp only [causalSupport, Finset.mem_filter, Finset.mem_univ, true_and]
  cases a with
  | none => exact TemporalReach.stay .zero
  | some a =>
      apply TemporalReach.send .zero
      rw [Nat.add_zero, starRound]
      exact Nat.zero_lt_one

theorem star_exposes_nodes (coeff size : I → Nat)
    (G : Nat → Agent size → Agent size → Nat) (r : Nat)
    (starRound : G (r+1) = star coeff size) :
    visibleNodes G (leader size) r 1 none = Finset.univ := by
  classical
  apply Finset.eq_univ_of_forall
  intro node
  apply Finset.mem_image.mpr
  exact ⟨node.out, by rw [star_exposes_support coeff size G r starRound]; exact Finset.mem_univ _,
    classOf_out G (leader size) r node⟩

/-- Every level through B−1 is exhaustive in the final leader vista. -/
theorem final_visible_prefix (coeff size : I → Nat) (B : Nat) (positive : 0 < B)
    (r : Nat) (before : r < B) :
    CoreTiming.levelsAt (network coeff size B) (leader size) B none r = Finset.univ := by
  have previous : B-1+1 = B := by omega
  have finalRound : network coeff size B (B-1+1) = star coeff size := by
    rw [previous]
    exact network_after coeff size B B le_rfl
  have visible := star_exposes_nodes coeff size (network coeff size B) (B-1) finalRound
  have delay : B-(B-1) = 1 := by omega
  apply HistoryPrefix.exhaustive_prefix_at_round _ _ B r (B-1) none (by omega) (by omega)
  simpa only [delay] using visible

namespace X3CBaseline
variable {q m : Nat} (inst : X3C.Instance q m)

noncomputable def graph : Nat → Agent (X3C.baselineGroups q m) → Agent (X3C.baselineGroups q m) → Nat :=
  network inst.coefficient (X3C.baselineGroups q m) (X3C.base q)

theorem order : Fintype.card (Agent (X3C.baselineGroups q m)) = X3C.baselineMass q m + 1 :=
  (population (X3C.baselineGroups q m)).trans X3C.baselineGroups_order

theorem admissible (large : 2 ≤ q) : Admissible 1 (graph inst) (leader (X3C.baselineGroups q m)) :=
  network_admissible _ _ _ (inst.coefficient_positive large)

theorem loopless (round : Nat) (a : Agent (X3C.baselineGroups q m)) : (graph inst) round a a = 0 :=
  network_loopless _ _ _ _ _

theorem visible_prefix (r : Nat) (before : r < X3C.base q) :
    CoreTiming.levelsAt (graph inst) (leader (X3C.baselineGroups q m)) (X3C.base q) none r = Finset.univ :=
  final_visible_prefix inst.coefficient (X3C.baselineGroups q m) (X3C.base q)
    (by simp [X3C.base]) r before

end X3CBaseline
end Counting.HardnessBaseline
