import Counting.LowerAllLeaders
import Counting.LowerOneLeader

/-!
# Correctness and lower bounds with a fixed leader count

The paper compares different population sizes at the same supplied number
of leaders. Correctness below therefore quantifies over all admissible finite
populations at one fixed `ell`, without constraining any other leader count.
-/

namespace Counting

/-- Counting correctness for all admissible populations at one fixed leader
count. The protocol does not receive the population size. -/
def Protocol.SolvesCountingFor {State : Type} (P : Protocol State) (ell : Nat) : Prop :=
  ∀ (V : Type) [Fintype V] (G : Nat → V → V → Nat)
    (leader : V → Bool), Admissible ell G leader →
    (∀ t x s k, P.trace ell G leader t x = .halted s k → k = Fintype.card V) ∧
    (∃ t, ∀ x, ∃ s, P.trace ell G leader t x = .halted s (Fintype.card V))

/-- The uniform interface is precisely fixed-count correctness for every
leader count; neither formulation bounds the admissible population size. -/
theorem Protocol.solvesCounting_iff_forall_leaders {State : Type} (P : Protocol State) :
    P.SolvesCounting ↔ ∀ ell, P.SolvesCountingFor ell := by
  constructor
  · intro correct ell V _ G leader valid
    exact correct V ell G leader valid
  · intro correct V _ ell G leader valid
    exact correct ell V G leader valid

/-- Indistinguishability needs correctness only at the common leader count. -/
theorem universal_lower_bound_for {State V W : Type} [Fintype V] [Fintype W]
    (P : Protocol State) (ell : Nat) (correct : P.SolvesCountingFor ell)
    (G : Nat → V → V → Nat) (H : Nat → W → W → Nat)
    (leaderV : V → Bool) (leaderW : W → Bool)
    (validV : Admissible ell G leaderV) (validW : Admissible ell H leaderW)
    (t : Nat) (x : V) (y : W)
    (different : Fintype.card V ≠ Fintype.card W)
    (common : history G leaderV t x = history H leaderW t y) :
    ∃ s, P.trace ell G leaderV t x = .active s := by
  exact P.common_history_prevents_halting ell G H leaderV leaderW t x y common different
    (fun s k hk => (correct V G leaderV validV).1 t x s k hk)
    (fun s k hk => (correct W H leaderW validW).1 t y s k hk)

namespace LowerAllLeaders

/-- The all-leader lower bound requires correctness for fixed `ell=n` only. -/
theorem all_leaders_lower_bound_for {State : Type} (P : Protocol State) (k : Nat)
    (correct : P.SolvesCountingFor (k + 1)) :
    ∃ s, P.trace (k + 1) (network (k + 1)) (allLeaders k) k 0 = .active s := by
  apply universal_lower_bound_for P (k + 1) correct
    (network (k + 1)) (network (k + 1 + 1)) (allLeaders k) (extendedLeaders k)
    (small_admissible k) (large_admissible k) k 0 0
  · simp
  · exact endpoint_common_prefix k

/-- The endpoint of the all-leader order-`n` path cannot halt before round `n`,
even when the protocol is required to solve counting only for `ell=n`. -/
theorem endpoint_halt_round_ge_order_for {State : Type} (P : Protocol State)
    (k time : Nat) (correct : P.SolvesCountingFor (k + 1))
    (state : State) (output : Nat)
    (halted : P.trace (k + 1) (network (k + 1)) (allLeaders k) time 0 =
      .halted state output) : k + 1 ≤ time := by
  by_contra h
  have ht : time ≤ k := by omega
  obtain ⟨activeState, hactive⟩ := all_leaders_lower_bound_for P k correct
  have hlate := P.halted_forever (k + 1) (network (k + 1)) (allLeaders k)
    time 0 state output halted (k - time)
  have heq : time + (k - time) = k := by omega
  rw [heq, hactive] at hlate
  cases hlate

end LowerAllLeaders

namespace LowerOneLeader

/-- The one-leader lower bound needs correctness only at `ell=1`. -/
theorem one_leader_lower_bound_for {State : Type} (P : Protocol State)
    (correct : P.SolvesCountingFor 1) (k : Nat) :
    ∃ s, P.trace 1 (network k) (leader k) (2 * (k + 1)) 0 = .active s := by
  apply universal_lower_bound_for P 1 correct (network k) (network (k + 1))
    (leader k) (leader (k + 1)) (admissible k) (admissible (k + 1))
    (2 * (k + 1)) 0 0
  · simp
  · exact endpoint_common_prefix k

/-- At fixed `ell=1`, the endpoint leader of the looped path still requires
at least `2n-1` rounds, for every `n≥2`. -/
theorem endpoint_halt_round_ge_two_mul_sub_one_for {State : Type} (P : Protocol State)
    (correct : P.SolvesCountingFor 1) (k time : Nat) (state : State) (output : Nat)
    (halted : P.trace 1 (network k) (leader k) time 0 = .halted state output) :
    2 * (k + 2) - 1 ≤ time := by
  by_contra h
  have ht : time ≤ 2 * (k + 1) := by omega
  obtain ⟨activeState, hactive⟩ := one_leader_lower_bound_for P correct k
  have hlate := P.halted_forever 1 (network k) (leader k)
    time 0 state output halted (2 * (k + 1) - time)
  have heq : time + (2 * (k + 1) - time) = 2 * (k + 1) := by omega
  rw [heq, hactive] at hlate
  cases hlate

end LowerOneLeader
end Counting
