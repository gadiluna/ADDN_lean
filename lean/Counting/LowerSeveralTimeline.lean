import Counting.LowerSeveralBounds
import Counting.FixedLeaders

/-! Lifting the phase invariants to actual full-information histories. -/

namespace Counting.LowerSeveralPhases

/-- The first phase on an arbitrary pair of actual executions, starting from
any offset at which the phase invariant has been established. -/
theorem first_phase_histories (k g offset : Nat)
    (G : Nat → Small k g → Small k g → Nat) (H : Nat → Large k g → Large k g → Nat)
    (labels : Small k g → Bool) (labels' : Large k g → Bool)
    (initial : FirstMatched k g 0 (history G labels offset) (history H labels' offset))
    (smallRounds : ∀ t, t < k + 1 → G (offset + t + 1) = firstSmall k g)
    (largeRounds : ∀ t (ht : t < k + 1), H (offset + t + 1) =
      firstLarge k g ⟨t, by omega⟩) :
    ∀ t, t ≤ k + 1 → FirstMatched k g t
      (history G labels (offset + t)) (history H labels' (offset + t)) := by
  intro t
  induction t with
  | zero => intro _; simpa using initial
  | succ t ih =>
      intro ht
      have hprev := ih (by omega)
      have hstep := first_step_preserves k g ⟨t, by omega⟩ _ _ hprev
      simp only [Nat.add_succ]
      change FirstMatched k g (t + 1)
        (step (G (offset + t + 1)) (history G labels (offset + t)))
        (step (H (offset + t + 1)) (history H labels' (offset + t)))
      rw [smallRounds t (by omega), largeRounds t (by omega)]
      exact hstep

/-- The second phase consumes the remaining matching centers in the
specified order and retains the observers and final original nonleaders. -/
theorem second_phase_histories (k g offset : Nat)
    (G : Nat → Small k g → Small k g → Nat) (H : Nat → Large k g → Large k g → Nat)
    (labels : Small k g → Bool) (labels' : Large k g → Bool)
    (initial : SecondMatched k g 0 (history G labels offset) (history H labels' offset))
    (smallRounds : ∀ t (ht : t < k + 1), G (offset + t + 1) =
      secondSmall k g ⟨t, by omega⟩)
    (largeRounds : ∀ t (ht : t < k + 1), H (offset + t + 1) =
      secondLarge k g ⟨t, by omega⟩) :
    ∀ t, t ≤ k + 1 → SecondMatched k g t
      (history G labels (offset + t)) (history H labels' (offset + t)) := by
  intro t
  induction t with
  | zero => intro _; simpa using initial
  | succ t ih =>
      intro ht
      have hprev := ih (by omega)
      have hstep := second_step_preserves k g ⟨t, by omega⟩ _ _ hprev
      simp only [Nat.add_succ]
      change SecondMatched k g (t + 1)
        (step (G (offset + t + 1)) (history G labels (offset + t)))
        (step (H (offset + t + 1)) (history H labels' (offset + t)))
      rw [smallRounds t (by omega), largeRounds t (by omega)]
      exact hstep

end Counting.LowerSeveralPhases
