import Counting.LowerSeveralSchedule
import Counting.LowerSeveralInitial

/-!
# The several-leader common-history construction and lower bound

For every k,g≥0 these executions have ell=k+2 leaders and orders
n=k+g+3 and n+ell−1. Their designated leaders have identical full histories
through round 2n−3, on loopless strongly connected graphs with multiplicity
at most ell and outdegree at most ell². The protocol conclusion requires
correctness for all populations at this fixed leader count, including
protocols whose halted agents are silent.
-/

namespace Counting.LowerSeveral
open LowerSeveralPhases

/-- Equality of full histories includes equality at every earlier round. -/
theorem history_eq_of_le {V W : Type} [Fintype V] [Fintype W]
    (G : Nat → V → V → Nat) (H : Nat → W → W → Nat)
    (labels : V → Bool) (labels' : W → Bool) (x : V) (y : W)
    (s t : Nat) (hst : s ≤ t)
    (common : history G labels t x = history H labels' t y) :
    history G labels s x = history H labels' s y := by
  induction t with
  | zero =>
      have hs : s = 0 := by omega
      subst s
      exact common
  | succ t ih =>
      by_cases hs : s = t + 1
      · subst s
        exact common
      · apply ih (by omega)
        exact congrArg Prod.fst common

theorem end_initial_matched (k g : Nat) :
    FirstMatched k g 0
      (history (smallNetwork k g) LowerSeveralRelay.leader g)
      (history (largeNetwork k g) LowerSeveralRelay.leader g) := by
  apply LowerSeveralInitial.initial_histories
  · intro t _ ht
    exact small_initial_round k g t ht
  · intro t _ ht
    exact large_initial_round k g t ht

theorem end_first_matched (k g : Nat) :
    FirstMatched k g (k + 1)
      (history (smallNetwork k g) LowerSeveralRelay.leader (g + (k + 1)))
      (history (largeNetwork k g) LowerSeveralRelay.leader (g + (k + 1))) := by
  exact first_phase_histories k g g (smallNetwork k g) (largeNetwork k g)
    LowerSeveralRelay.leader LowerSeveralRelay.leader (end_initial_matched k g)
    (small_first_round k g) (large_first_round k g) (k + 1) le_rfl

theorem end_second_matched (k g : Nat) :
    SecondMatched k g (k + 1)
      (history (smallNetwork k g) LowerSeveralRelay.leader (g + (k + 1) + (k + 1)))
      (history (largeNetwork k g) LowerSeveralRelay.leader (g + (k + 1) + (k + 1))) := by
  exact second_phase_histories k g (g + (k + 1)) (smallNetwork k g) (largeNetwork k g)
    LowerSeveralRelay.leader LowerSeveralRelay.leader
    (first_to_second k g _ _ (end_first_matched k g))
    (small_second_round k g) (large_second_round k g) (k + 1) le_rfl

/-- Equality at the last common round, with no bound on the number of relays. -/
theorem endpoint_common_history (k g : Nat) :
    history (smallNetwork k g) LowerSeveralRelay.leader (2 * (k + g + 3) - 3)
      (smallLeader k g (observer k)) =
    history (largeNetwork k g) LowerSeveralRelay.leader (2 * (k + g + 3) - 3)
      (largeLeader k g (observer k)) := by
  obtain ⟨hobservers, hnonleaders, hrelays⟩ :=
    second_final_matches k g _ _ (end_second_matched k g)
  have h := LowerSeveralFinal.final_histories k g (g + (k + 1) + (k + 1))
    (smallNetwork k g) (largeNetwork k g) LowerSeveralRelay.leader LowerSeveralRelay.leader
    (LowerSeveralFinal.tail_matches_of_middle k g _ _ hobservers hnonleaders hrelays)
    (fun t _ => small_final_round k g t) (fun t _ => large_final_round k g t)
    (g + 1) le_rfl
  have heq : g + (k + 1) + (k + 1) + (g + 1) = 2 * (k + g + 3) - 3 := by omega
  exact heq ▸ h

/-- The complete common interval, including every intermediate phase. -/
theorem endpoint_common_prefix (k g t : Nat) (ht : t ≤ 2 * (k + g + 3) - 3) :
    history (smallNetwork k g) LowerSeveralRelay.leader t (smallLeader k g (observer k)) =
      history (largeNetwork k g) LowerSeveralRelay.leader t (largeLeader k g (observer k)) :=
  history_eq_of_le _ _ _ _ _ _ t _ ht (endpoint_common_history k g)

/-- The theorem's original parameters: every n>ell≥2 is covered. The two
graphs are explicitly defined, and their structural bounds hold forever. -/
theorem several_leader_common_vista (n ell : Nat) (hell : 2 ≤ ell) (hn : ell < n) :
    let k := ell - 2
    let g := n - ell - 1
    Fintype.card (Small k g) = n ∧ Fintype.card (Large k g) = n + ell - 1 ∧
    Admissible ell (smallNetwork k g) LowerSeveralRelay.leader ∧
    Admissible ell (largeNetwork k g) LowerSeveralRelay.leader ∧
    (∀ t, RoundValid (smallNetwork k g t) ell ∧ RoundValid (largeNetwork k g t) ell) ∧
    (∀ t, t ≤ 2 * n - 3 →
      history (smallNetwork k g) LowerSeveralRelay.leader t (smallLeader k g (observer k)) =
        history (largeNetwork k g) LowerSeveralRelay.leader t (largeLeader k g (observer k))) := by
  dsimp only
  have hell' : ell - 2 + 2 = ell := by omega
  have hn' : ell - 2 + (n - ell - 1) + 3 = n := by omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [small_order, hn']
  · rw [large_order]
    omega
  · simpa only [hell'] using small_admissible (ell - 2) (n - ell - 1)
  · simpa only [hell'] using large_admissible (ell - 2) (n - ell - 1)
  · intro t
    constructor
    · simpa only [hell'] using small_valid (ell - 2) (n - ell - 1) t
    · simpa only [hell'] using large_valid (ell - 2) (n - ell - 1) t
  · intro t ht
    exact endpoint_common_prefix _ _ t (by simpa only [hn'] using ht)

/-- Common full histories keep the smaller observer active in every correct
protocol, even if correctness is required only for this leader count. -/
theorem several_leaders_lower_bound_for {State : Type} (P : Protocol State) (k g : Nat)
    (correct : P.SolvesCountingFor (k + 2)) :
    ∃ s, P.trace (k + 2) (smallNetwork k g) LowerSeveralRelay.leader
      (2 * (k + g + 3) - 3) (smallLeader k g (observer k)) = .active s := by
  exact universal_lower_bound_for P (k + 2) correct
    (smallNetwork k g) (largeNetwork k g) LowerSeveralRelay.leader LowerSeveralRelay.leader
    (small_admissible k g) (large_admissible k g)
    (2 * (k + g + 3) - 3) (smallLeader k g (observer k)) (largeLeader k g (observer k))
    (different_orders k g) (endpoint_common_history k g)

/-- The order-n observer cannot halt before round 2n−2. -/
theorem endpoint_halt_round_ge_two_mul_sub_two_for {State : Type} (P : Protocol State)
    (k g time : Nat) (correct : P.SolvesCountingFor (k + 2))
    (state : State) (output : Nat)
    (halted : P.trace (k + 2) (smallNetwork k g) LowerSeveralRelay.leader time
      (smallLeader k g (observer k)) = .halted state output) :
    2 * (k + g + 3) - 2 ≤ time := by
  by_contra h
  have ht : time ≤ 2 * (k + g + 3) - 3 := by omega
  obtain ⟨activeState, hactive⟩ := several_leaders_lower_bound_for P k g correct
  have hlate := P.halted_forever (k + 2) (smallNetwork k g) LowerSeveralRelay.leader
    time (smallLeader k g (observer k)) state output halted (2 * (k + g + 3) - 3 - time)
  have heq : time + (2 * (k + g + 3) - 3 - time) = 2 * (k + g + 3) - 3 := by omega
  rw [heq, hactive] at hlate
  cases hlate

/-- The universal lower bound in the paper's n,ell notation. -/
theorem several_leaders_lower_bound {State : Type} (P : Protocol State)
    (n ell : Nat) (hell : 2 ≤ ell) (hn : ell < n) (correct : P.SolvesCountingFor ell)
    (time : Nat) (state : State) (output : Nat)
    (halted : P.trace ell (smallNetwork (ell - 2) (n - ell - 1)) LowerSeveralRelay.leader time
      (smallLeader (ell - 2) (n - ell - 1) (observer (ell - 2))) = .halted state output) :
    2 * n - 2 ≤ time := by
  have hell' : ell - 2 + 2 = ell := by omega
  have hn' : ell - 2 + (n - ell - 1) + 3 = n := by omega
  have h := endpoint_halt_round_ge_two_mul_sub_two_for P (ell - 2) (n - ell - 1) time
    (by simpa only [hell'] using correct) state output (by simpa only [hell'] using halted)
  simpa only [hn'] using h

end Counting.LowerSeveral
