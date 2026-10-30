import Counting.LowerSeveralExact

/-! The numerical and semantic effect of adding one further relay to each
execution: both populations grow by one, the leader count stays fixed,
and the exact last common round grows by two. -/

namespace Counting.LowerSeveral
open LowerSeveralPhases LowerSeveralExact

theorem two_round_extension (k g : Nat) :
    Fintype.card (Small k (g + 1)) = Fintype.card (Small k g) + 1 ∧
    Fintype.card (Large k (g + 1)) = Fintype.card (Large k g) + 1 ∧
    Admissible (k + 2) (smallNetwork k (g + 1)) LowerSeveralRelay.leader ∧
    Admissible (k + 2) (largeNetwork k (g + 1)) LowerSeveralRelay.leader ∧
    2 * (k + (g + 1) + 3) - 3 = (2 * (k + g + 3) - 3) + 2 ∧
    (∀ t, t ≤ (2 * (k + g + 3) - 3) + 2 →
      history (smallNetwork k (g + 1)) LowerSeveralRelay.leader t
          (smallLeader k (g + 1) (observer k)) =
        history (largeNetwork k (g + 1)) LowerSeveralRelay.leader t
          (largeLeader k (g + 1) (observer k))) ∧
    (history (smallNetwork k (g + 1)) LowerSeveralRelay.leader ((2 * (k + g + 3) - 3) + 3)
        (smallLeader k (g + 1) (observer k)) ≠
      history (largeNetwork k (g + 1)) LowerSeveralRelay.leader ((2 * (k + g + 3) - 3) + 3)
        (largeLeader k (g + 1) (observer k))) := by
  refine ⟨?_, ?_, small_admissible k (g + 1), large_admissible k (g + 1), ?_, ?_, ?_⟩
  · rw [small_order, small_order]
    omega
  · rw [large_order, large_order]
    omega
  · omega
  · intro t ht
    exact endpoint_common_prefix k (g + 1) t (by omega)
  · have htime : 2 * (k + (g + 1) + 3) - 2 = (2 * (k + g + 3) - 3) + 3 := by omega
    exact htime ▸ endpoint_first_difference k (g + 1)

end Counting.LowerSeveral
