import Counting.LowerSeveral

/-! The endpoint of the common interval is exact: the fixed final cycles
first distinguish the designated leaders at round 2n−2. -/

namespace Counting.LowerSeveralExact
open LowerSeveralPhases LowerSeveralFinal LowerSeveral

def penultimate (k : Nat) : Leaders k := ⟨k, by omega⟩

theorem small_original_incoming {A : Type} (k g : Nat) (state : Small k g → A) :
    incoming (smallGraph k g) state (smallNonleader k g) =
      {state (smallLeader k g (penultimate k))} := by
  unfold smallGraph
  rw [relabel_incoming]
  have h := graph_incoming_of_consecutive k 0 g (state ∘ (smallEquiv k g).symm)
    (.inl (.inl (penultimate k))) (.inl (.inr 0)) (by
      simp [rank, penultimate])
  exact h

theorem large_original_incoming {A : Type} (k g : Nat) (state : Large k g → A) :
    incoming (largeGraph k g) state (largeNonleader k g (observer k)) =
      {state (largeNonleader k g (penultimate k))} := by
  apply graph_incoming_of_consecutive k (k + 1) g
  simp [rank, largeNonleader, penultimate, observer]
  omega

/-- The two incoming predecessors of the final original nonleaders have
different initial leader labels at every full-history depth. -/
theorem predecessor_histories_differ (k g t : Nat)
    (G : Nat → Small k g → Small k g → Nat) (H : Nat → Large k g → Large k g → Nat) :
    history G LowerSeveralRelay.leader t (smallLeader k g (penultimate k)) ≠
      history H LowerSeveralRelay.leader t (largeNonleader k g (penultimate k)) := by
  intro heq
  have h := history_eq_of_le G H LowerSeveralRelay.leader LowerSeveralRelay.leader
    _ _ 0 t (Nat.zero_le _) heq
  cases h

/-- The first final cycle round creates a difference at the first position
of the shared suffix, irrespective of the preceding graph sequence. -/
theorem first_tail_difference (k g offset : Nat)
    (G : Nat → Small k g → Small k g → Nat) (H : Nat → Large k g → Large k g → Nat)
    (smallRound : G (offset + 1) = smallGraph k g)
    (largeRound : H (offset + 1) = largeGraph k g) :
    history G LowerSeveralRelay.leader (offset + 1) (smallTail k g 0) ≠
      history H LowerSeveralRelay.leader (offset + 1) (largeTail k g 0) := by
  intro heq
  have hin := congrArg (fun h : FullHistory (offset + 1) => h.2.2) heq
  change incoming (G (offset + 1)) (history G LowerSeveralRelay.leader offset) (smallTail k g 0) =
    incoming (H (offset + 1)) (history H LowerSeveralRelay.leader offset) (largeTail k g 0) at hin
  rw [smallRound, largeRound, smallTail_zero, largeTail_zero,
    small_original_incoming, large_original_incoming] at hin
  exact predecessor_histories_differ k g offset G H (Multiset.singleton_inj.mp hin)

/-- The newly created difference traverses one suffix edge per final round. -/
theorem tail_difference (k g offset : Nat)
    (G : Nat → Small k g → Small k g → Nat) (H : Nat → Large k g → Large k g → Nat)
    (smallRounds : ∀ t, G (offset + t + 1) = smallGraph k g)
    (largeRounds : ∀ t, H (offset + t + 1) = largeGraph k g) :
    ∀ t (ht : t ≤ g + 1),
      history G LowerSeveralRelay.leader (offset + t + 1) (smallTail k g ⟨t, by omega⟩) ≠
        history H LowerSeveralRelay.leader (offset + t + 1) (largeTail k g ⟨t, by omega⟩) := by
  intro t
  induction t with
  | zero =>
      intro ht
      exact first_tail_difference k g offset G H (smallRounds 0) (largeRounds 0)
  | succ t ih =>
      intro ht heq
      have hin := congrArg (fun h : FullHistory (offset + (t + 1) + 1) => h.2.2) heq
      change incoming (G (offset + (t + 1) + 1))
          (history G LowerSeveralRelay.leader (offset + (t + 1))) (smallTail k g ⟨t + 1, by omega⟩) =
        incoming (H (offset + (t + 1) + 1))
          (history H LowerSeveralRelay.leader (offset + (t + 1))) (largeTail k g ⟨t + 1, by omega⟩) at hin
      rw [smallRounds, largeRounds] at hin
      have hs := congrArg (fun h : FullHistory (offset + (t + 1) + 1) => h.2.2)
        (smallTail_step k g (history G LowerSeveralRelay.leader (offset + (t + 1)))
          ⟨t + 1, by omega⟩ (by change 0 < t + 1; omega))
      have hl := congrArg (fun h : FullHistory (offset + (t + 1) + 1) => h.2.2)
        (largeTail_step k g (history H LowerSeveralRelay.leader (offset + (t + 1)))
          ⟨t + 1, by omega⟩ (by change 0 < t + 1; omega))
      dsimp only [step] at hs hl
      rw [hs, hl] at hin
      have hprev : previousTail g ⟨t + 1, by omega⟩ = (⟨t, by omega⟩ : Fin (g + 2)) := by
        apply Fin.ext
        simp [previousTail]
      rw [hprev] at hin
      exact ih (by omega) (Multiset.singleton_inj.mp hin)

/-- The construction's observers first differ at round 2n−2. -/
theorem endpoint_first_difference (k g : Nat) :
    history (smallNetwork k g) LowerSeveralRelay.leader (2 * (k + g + 3) - 2)
        (smallLeader k g (observer k)) ≠
      history (largeNetwork k g) LowerSeveralRelay.leader (2 * (k + g + 3) - 2)
        (largeLeader k g (observer k)) := by
  have h := tail_difference k g (g + (k + 1) + (k + 1))
    (smallNetwork k g) (largeNetwork k g) (small_final_round k g) (large_final_round k g)
    (g + 1) le_rfl
  have hlast : (⟨g + 1, by omega⟩ : Fin (g + 2)) = Fin.last (g + 1) := rfl
  simp only [hlast, smallTail_last, largeTail_last] at h
  have htime : g + (k + 1) + (k + 1) + (g + 1) + 1 = 2 * (k + g + 3) - 2 := by omega
  exact htime ▸ h

end Counting.LowerSeveralExact
