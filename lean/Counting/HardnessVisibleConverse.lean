import Counting.HardnessVisibleBounds
import Counting.RealizabilityComplete

namespace Counting.HardnessVisible
open DirectedCounting PaperHistory TimingProtocolLocal HardnessPath HardnessBaseline
open scoped BigOperators Classical

variable {V : Type} [Fintype V]
variable (G : Nat → V → V → Nat) (leader : V → Bool)
variable {q m : Nat} (inst : X3C.Instance q m)

/-- Once level one is exhaustive, the unique leader's entire outgoing degree
is accounted for by the visible nonleader groups. Its displayed record rules
out a leader loop, so the former inequality is now the exact X3C equation. -/
theorem group_weighted_equation (large : 2 ≤ q) (network : Admissible 1 G leader) (observer : V)
    (same : history G leader (X3C.base q) observer = X3CBaseline.leaderView inst) :
    (∑ i, inst.coefficient i * (group G leader inst i).card) = inst.weightedTarget := by
  classical
  have exhaustive := (first_level_exhaustive G leader inst large network observer same).1
  rw [first_represented_partition G leader inst network observer same] at exhaustive
  rw [← groupUnion_receipts G leader inst large network observer same,
    ← observer_degree G leader inst observer same, ← exhaustive,
    Finset.sum_insert (observer_not_groupUnion G leader inst observer same),
    observer_loop_zero G leader inst network observer same, zero_add]

theorem population_groupOrder (large : 2 ≤ q) (network : Admissible 1 G leader) (observer : V)
    (same : history G leader (X3C.base q) observer = X3CBaseline.leaderView inst) :
    Fintype.card V = X3C.groupOrder (fun i => (group G leader inst i).card) := by
  have count := first_represented_card G leader inst large network observer same
  rw [(first_level_exhaustive G leader inst large network observer same).1, Finset.card_univ] at count
  exact count

/-- Every admissible realization has the baseline order or the exact-cover
order. In the latter case an actual exact cover exists in the source instance. -/
theorem population_dichotomy (large : 2 ≤ q) (network : Admissible 1 G leader) (observer : V)
    (same : history G leader (X3C.base q) observer = X3CBaseline.leaderView inst) :
    Fintype.card V = X3C.baselineMass q m+1 ∨
      (Fintype.card V = X3C.baselineMass q m+q ∧ ∃ chosen, inst.IsExactCover chosen) := by
  rw [population_groupOrder G leader inst large network observer same]
  exact inst.shifted_order_dichotomy large _ (group_lower G leader inst observer same)
    (group_weighted_equation G leader inst large network observer same)

/-- The converse quantifies over all finite carriers in Realizable, rather
than just the path networks used to produce the reduction. -/
theorem realization_dichotomy (large : 2 ≤ q) (N : Nat)
    (realized : Realizability.Realizable 1 N (X3CBaseline.leaderView inst)) :
    N = X3C.baselineMass q m+1 ∨
      (N = X3C.baselineMass q m+q ∧ ∃ chosen, inst.IsExactCover chosen) := by
  obtain ⟨A, finite, graphs, labels, observer, order, network, same⟩ := realized
  letI : Fintype A := finite
  simpa only [order] using population_dichotomy graphs labels inst large network observer same

end Counting.HardnessVisible
