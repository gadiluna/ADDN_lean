import Counting.CoreCompleteness
import Counting.HistoryPrefix

/-! The mathematical core certificate at the actual observer's round 2n-1.
ExecutableRefinementCoreCorrectness connects these semantic results to the
executable protocol. No protocol termination conclusion is assumed here.
-/

namespace Counting.CoreTiming
open DirectedCounting PaperHistory

variable {V : Type} [Fintype V]
variable (G : Nat → V → V → Nat) (leader : V → Bool)

noncomputable def levelsAt (round : Nat) (observer : V) :
    ∀ r, Finset (Node G leader r) :=
  fun r => visibleNodes G leader r (round - r) observer

theorem core_prefix_exhaustive
    (connected : ∀ t, 0 < t → StronglyConnected (fun u v => 0 < G t u v))
    (observer : V) (r : Nat) (hr : r ≤ Fintype.card V) :
    levelsAt G leader (2 * Fintype.card V - 1) observer r = Finset.univ := by
  apply vista_level_exhaustive G leader connected
  omega

/-- At round 2n-1 every observer has a passing mathematical core certificate,
and the selected anchor equations have exactly one rational solution. -/
theorem true_candidate_at_core_round
    (positiveLeaders : 0 < FlatHistory.leaderCount leader)
    (connected : ∀ t, 0 < t → StronglyConnected (fun u v => 0 < G t u v))
    (observer : V) :
    ∃ r, r < Fintype.card V ∧
      Nonempty (CoreHistory.Checks G leader (Fintype.card V) (r + 1)
        (levelsAt G leader (2 * Fintype.card V - 1) observer) (anonymity G leader)) ∧
      ∃! z : Node G leader (r + 1) → ℚ,
        FlatLevel.Flow (fun i j => (FlatHistory.weight G leader r i j : ℚ))
          (fun i => (outdegreeLabel G leader r i : ℚ)) z ∧
        (∑ i ∈ FlatHistory.leaders G leader r, z i) = (FlatHistory.leaderCount leader : ℚ) :=
  CoreCompleteness.exists_true_candidate_with_unique_anchor G leader positiveLeaders connected
    _ (fun r hr => core_prefix_exhaustive G leader connected observer r hr)

/-- A wrong candidate cannot pass the mathematical core checks at any round. -/
theorem false_candidate_has_no_certificate
    (connected : ∀ t, 0 < t → StronglyConnected (fun u v => 0 < G t u v))
    (observer : V) (round m h : Nat) (wrong : m ≠ Fintype.card V)
    (candidate : ∀ r, Node G leader r → Nat) :
    IsEmpty (CoreHistory.Checks G leader m h (levelsAt G leader round observer) candidate) :=
  ⟨fun checks => wrong (checks.accepted_candidate_eq_population connected)⟩

end Counting.CoreTiming
