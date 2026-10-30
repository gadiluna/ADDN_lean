import Counting.LowerSeveralInitialSteps

/-! Indistinguishability during the g initial relay rounds. All original
nonleaders remain matched, including when the larger side has ell of them. -/

namespace Counting.LowerSeveralInitial
open DirectedCounting LowerSeveralPhases

structure InitialMatched {A : Type} (k g t : Nat) (a : Small k g → A) (b : Large k g → A) : Prop
    extends FirstMatched k g 0 a b where
  tail_ordinary : ∀ j : Fin g, t ≤ j.val → a (.inr j) = a (smallNonleader k g)

/-- One initial round propagates the exceptional relay state by one
position, while all original nonleaders still receive the common old state. -/
theorem initial_step_preserves {A : Type} (k g t : Nat) (before : t < g)
    (a : Small k g → A) (b : Large k g → A) (h : InitialMatched k g t a b) :
    InitialMatched k g (t + 1) (step (initialSmall k g) a) (step (initialLarge k g) b) := by
  have hg : 0 < g := by omega
  simp only [initialSmall, initialLarge, if_pos hg]
  let last : Fin g := ⟨g - 1, by omega⟩
  have nonleaders : ∀ v, a (.inl (.inr ())) = b (.inl (.inr v)) := h.nonleaders
  have lastOrd : a (.inr last) = a (smallNonleader k g) := h.tail_ordinary last (by dsimp [last]; omega)
  have smallStep : step (delayGraph unitFin k g) a (smallNonleader k g) =
      (a (smallNonleader k g), 1, {a (smallNonleader k g)}) := by
    rw [show smallNonleader k g = .inl (.inr ()) from rfl,
      delay_original_first_step unitFin k g hg a () rfl]
    exact congrArg (fun s => (a (smallNonleader k g), 1, ({s} : Multiset A))) lastOrd
  have leadersSum : (∑ l : Leaders k, ({a (.inl (.inl l))} : Multiset A)) =
      ∑ l : Leaders k, ({b (.inl (.inl l))} : Multiset A) := by
    apply Finset.sum_congr rfl
    intro l _
    exact congrArg (fun s => ({s} : Multiset A))
      ((h.small_leaders l).trans (h.leaders l (Nat.zero_le _)))
  refine {
    small_leaders := ?_
    leaders := ?_
    nonleaders := ?_
    relays := ?_
    tail_ordinary := ?_
  }
  · intro l
    change step _ a (.inl (.inl l)) = step _ a (.inl (.inl (observer k)))
    rw [delay_leader_step _ _ _ hg, delay_leader_step _ _ _ hg]
    exact congrArg (fun s => (s, 1, ({a (.inr ⟨0, hg⟩)} : Multiset A))) (h.small_leaders l)
  · intro l _
    change step _ a (.inl (.inl (observer k))) = step _ b (.inl (.inl l))
    rw [delay_leader_step _ _ _ hg, delay_leader_step _ _ _ hg,
      h.relays ⟨0, hg⟩]
    exact congrArg (fun s => (s, 1, ({b (.inr ⟨0, hg⟩)} : Multiset A)))
      (h.leaders l (Nat.zero_le _))
  · intro v
    rw [smallStep]
    change _ = step (delayGraph (Equiv.refl (Leaders k)) k g) b (.inl (.inr v))
    by_cases hv : v.val = 0
    · rw [delay_original_first_step _ _ _ hg b v hv]
      rw [← nonleaders v, ← h.relays last, lastOrd]
      rfl
    · let u : Leaders k := ⟨v.val - 1, by have := v.isLt; omega⟩
      have next : u.val + 1 = v.val := by dsimp [u]; omega
      rw [delay_original_next_step _ _ _ hg b u v next,
        ← nonleaders v, ← nonleaders u]
      rfl
  · intro j
    by_cases hj : j.val = 0
    · have heq : j = ⟨0, hg⟩ := Fin.ext hj
      rw [heq, delay_relay_first_step unitFin k g hg a () rfl,
        delay_relay_first_step (Equiv.refl (Leaders k)) k g hg b (observer k)
          (by simp [observer]), h.relays ⟨0, hg⟩, leadersSum, nonleaders (observer k)]
    · let i : Fin g := ⟨j.val - 1, by have := j.isLt; omega⟩
      have next : i.val + 1 = j.val := by dsimp [i]; omega
      rw [delay_relay_next_step _ _ _ a i j next, delay_relay_next_step _ _ _ b i j next,
        h.relays j, h.relays i]
  · intro j hj
    let i : Fin g := ⟨j.val - 1, by have := j.isLt; omega⟩
    have next : i.val + 1 = j.val := by dsimp [i]; omega
    rw [delay_relay_next_step _ _ _ a i j next, smallStep,
      h.tail_ordinary j (by omega), h.tail_ordinary i (by dsimp [i]; omega)]

/-- The complete initial invariant in the actual global history semantics.
No premise mentions the future rounds or their graph choices. -/
theorem initial_invariant_histories (k g : Nat)
    (G : Nat → Small k g → Small k g → Nat) (H : Nat → Large k g → Large k g → Nat)
    (smallRounds : ∀ t, 0 < t → t ≤ g → G t = initialSmall k g)
    (largeRounds : ∀ t, 0 < t → t ≤ g → H t = initialLarge k g) :
    ∀ t, t ≤ g → InitialMatched k g t
      (history G LowerSeveralRelay.leader t) (history H LowerSeveralRelay.leader t) := by
  intro t
  induction t with
  | zero =>
      intro _
      exact {
        small_leaders := fun _ => rfl
        leaders := fun _ _ => rfl
        nonleaders := fun _ => rfl
        relays := fun _ => rfl
        tail_ordinary := fun _ _ => rfl
      }
  | succ t ih =>
      intro ht
      have prior := ih (by omega)
      have next := initial_step_preserves k g t (by omega)
        (history G LowerSeveralRelay.leader t) (history H LowerSeveralRelay.leader t) prior
      change InitialMatched k g (t + 1)
        (step (G (t + 1)) (history G LowerSeveralRelay.leader t))
        (step (H (t + 1)) (history H LowerSeveralRelay.leader t))
      rw [smallRounds (t + 1) (by omega) ht, largeRounds (t + 1) (by omega) ht]
      exact next

/-- After g initial rounds, all the hypotheses of the first middle phase
hold, also for g=0 where the initial phase has no communication rounds. -/
theorem initial_histories (k g : Nat)
    (G : Nat → Small k g → Small k g → Nat) (H : Nat → Large k g → Large k g → Nat)
    (smallRounds : ∀ t, 0 < t → t ≤ g → G t = initialSmall k g)
    (largeRounds : ∀ t, 0 < t → t ≤ g → H t = initialLarge k g) :
    FirstMatched k g 0 (history G LowerSeveralRelay.leader g) (history H LowerSeveralRelay.leader g) :=
  (initial_invariant_histories k g G H smallRounds largeRounds g le_rfl).toFirstMatched

end Counting.LowerSeveralInitial
