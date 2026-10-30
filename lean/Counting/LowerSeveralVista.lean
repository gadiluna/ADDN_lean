import Counting.LowerSeveralExact
import Counting.VistaIsomorphismActual

/-! The appendix construction stated directly for pointed isomorphisms of
the actual visible quotient history trees, rather than history equality. -/

namespace Counting.LowerSeveral
open LowerSeveralPhases VistaIsomorphism

/-- The several-leader common-vista theorem in its original parameters and
with its exact structural graph bounds. Both observers are leaders. -/
theorem several_leader_vista (n ell : Nat) (hell : 2 ≤ ell) (hn : ell < n) :
    let k := ell - 2
    let g := n - ell - 1
    Fintype.card (Small k g) = n ∧ Fintype.card (Large k g) = n + ell - 1 ∧
    Admissible ell (smallNetwork k g) LowerSeveralRelay.leader ∧
    Admissible ell (largeNetwork k g) LowerSeveralRelay.leader ∧
    (∀ t, RoundValid (smallNetwork k g t) ell ∧ RoundValid (largeNetwork k g t) ell) ∧
    LowerSeveralRelay.leader (smallLeader k g (observer k)) = true ∧
    LowerSeveralRelay.leader (largeLeader k g (observer k)) = true ∧
    (∀ t, t ≤ 2 * n - 3 → Nonempty (ActualIso (smallNetwork k g) (largeNetwork k g)
      LowerSeveralRelay.leader LowerSeveralRelay.leader t
      (smallLeader k g (observer k)) (largeLeader k g (observer k)))) := by
  obtain ⟨smallOrder, largeOrder, smallValid, largeValid, bounds, common⟩ :=
    several_leader_common_vista n ell hell hn
  refine ⟨smallOrder, largeOrder, smallValid, largeValid, bounds, rfl, rfl, ?_⟩
  intro t ht
  exact (actual_history_eq_iff_actualIso _ _ _ _ _ _ _).mp (common t ht)

/-- The two pointed vistas cease to be isomorphic in the first round
after the common interval. -/
theorem first_nonisomorphic_vistas (k g : Nat) :
    ¬ Nonempty (ActualIso (smallNetwork k g) (largeNetwork k g)
      LowerSeveralRelay.leader LowerSeveralRelay.leader (2 * (k + g + 3) - 2)
      (smallLeader k g (observer k)) (largeLeader k g (observer k))) := by
  intro iso
  exact LowerSeveralExact.endpoint_first_difference k g
    ((actual_history_eq_iff_actualIso _ _ _ _ _ _ _).mpr iso)

end Counting.LowerSeveral
