import Counting.LowerSeveralExtension
import Counting.TimingProtocolCorrectness

/-!
# A universal lower bound in all three regimes

The witness execution depends only on n and ell, and works for every
protocol correct on all populations at the fixed leader count ell.
The protocol may halt silently. No computational-cost or executable-code
assertion is made in this module.
-/

namespace Counting.LowerCombined
open TimingProtocol

/-- One concrete order-n execution on which every fixed-ell correct
protocol must wait until at least round T at a designated observer. -/
def HardExecution (n ell T : Nat) : Prop :=
  ∃ (V : Type) (finite : Fintype V),
    letI : Fintype V := finite
    ∃ (G : Nat → V → V → Nat) (leader : V → Bool) (observer : V),
      Fintype.card V = n ∧ Admissible ell G leader ∧
      ∀ (State : Type) (P : Protocol State), P.SolvesCountingFor ell →
        ∀ (time : Nat) (state : State) (output : Nat),
          P.trace ell G leader time observer = .halted state output → T ≤ time

theorem all_leaders_witness (k : Nat) : HardExecution (k + 1) (k + 1) (k + 1) := by
  refine ⟨Fin (k + 1), inferInstance, LowerAllLeaders.network (k + 1),
    LowerAllLeaders.allLeaders k, 0, Fintype.card_fin _, LowerAllLeaders.small_admissible k, ?_⟩
  intro State P correct time state output halted
  exact LowerAllLeaders.endpoint_halt_round_ge_order_for P k time correct state output halted

theorem one_leader_witness (k : Nat) : HardExecution (k + 2) 1 (2 * (k + 2) - 1) := by
  refine ⟨Fin (k + 2), inferInstance, LowerOneLeader.network k, LowerOneLeader.leader k, 0,
    Fintype.card_fin _, LowerOneLeader.admissible k, ?_⟩
  intro State P correct time state output halted
  exact LowerOneLeader.endpoint_halt_round_ge_two_mul_sub_one_for P correct k time state output halted

theorem several_leaders_witness (k g : Nat) :
    HardExecution (k + g + 3) (k + 2) (2 * (k + g + 3) - 2) := by
  refine ⟨LowerSeveralPhases.Small k g, inferInstance, LowerSeveral.smallNetwork k g,
    LowerSeveralRelay.leader, LowerSeveralPhases.smallLeader k g (LowerSeveralPhases.observer k),
    LowerSeveral.small_order k g, LowerSeveral.small_admissible k g, ?_⟩
  intro State P correct time state output halted
  exact LowerSeveral.endpoint_halt_round_ge_two_mul_sub_two_for P k g time correct state output halted

/-- Every admissible pair (n,ell) has a matching lower-bound execution. -/
theorem lower_bound (n ell : Nat) (positive : 1 ≤ ell) (population : ell ≤ n) :
    HardExecution n ell (optimizedTime n ell) := by
  by_cases all : n = ell
  · subst ell
    have hk : n - 1 + 1 = n := by omega
    simpa [hk, optimizedTime] using all_leaders_witness (n - 1)
  · by_cases one : ell = 1
    · subst ell
      have hk : n - 2 + 2 = n := by omega
      simpa [hk, optimizedTime, all] using one_leader_witness (n - 2)
    · have hk : ell - 2 + 2 = ell := by omega
      have hg : ell - 2 + (n - ell - 1) + 3 = n := by omega
      simpa only [hk, hg, optimizedTime, if_neg all, if_neg one] using
        several_leaders_witness (ell - 2) (n - ell - 1)

/-- The lower-bound witness has an active observer at every earlier time. -/
theorem HardExecution.before {n ell T : Nat} (hard : HardExecution n ell T) :
    ∃ (V : Type) (finite : Fintype V),
      letI : Fintype V := finite
      ∃ (G : Nat → V → V → Nat) (leader : V → Bool) (observer : V),
        Fintype.card V = n ∧ Admissible ell G leader ∧
        ∀ (State : Type) (P : Protocol State), P.SolvesCountingFor ell →
          ∀ t, t < T → ∃ state, P.trace ell G leader t observer = .active state := by
  obtain ⟨V, finite, G, leader, observer, order, valid, bound⟩ := hard
  letI : Fintype V := finite
  refine ⟨V, finite, G, leader, observer, order, valid, ?_⟩
  intro State P correct t before
  cases h : P.trace ell G leader t observer with
  | active state => exact ⟨state, rfl⟩
  | halted state output => have := bound State P correct t state output h; omega

end Counting.LowerCombined
