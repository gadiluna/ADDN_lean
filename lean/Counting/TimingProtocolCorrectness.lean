import Counting.TimingProtocol

namespace Counting.TimingProtocol
open DirectedCounting PaperHistory
open TimingProtocolLocal

variable {V : Type} [Fintype V]
variable (G : ℕ → V → V → ℕ) (leader : V → Bool)

theorem coreDecision_before (ell t : ℕ) (observer : V) (valid : Admissible ell G leader)
    (before : t < 2 * Fintype.card V - 1) :
    coreDecision ell t (history G leader t observer) = none := by
  classical
  unfold coreDecision
  dsimp only
  split
  · rename_i accepted
    have positive := valid.positive
    have pop := core_pass_sound G leader ell ((t + 1) / 2) t observer valid (by omega) accepted.2.2
    have scheduled := accepted.2.1
    omega
  · rfl

theorem coreDecision_at (ell : ℕ) (observer : V) (valid : Admissible ell G leader) :
    coreDecision ell (2 * Fintype.card V - 1) (history G leader (2 * Fintype.card V - 1) observer) =
      some (Fintype.card V) := by
  classical
  have positive : 0 < Fintype.card V := lt_of_lt_of_le valid.positive valid.leaderCount_le_card
  have candidate : (2 * Fintype.card V - 1 + 1) / 2 = Fintype.card V := by omega
  unfold coreDecision
  dsimp only
  rw [candidate, if_pos ⟨valid.leaderCount_le_card, rfl, true_core_pass G leader ell observer valid⟩]

theorem shortDecision_before (ell t : ℕ) (observer : V) (valid : Admissible ell G leader)
    (leaders : 2 ≤ ell) (before : t < 2 * Fintype.card V - 2) :
    shortDecision ell t (history G leader t observer) = none := by
  classical
  unfold shortDecision
  dsimp only
  split
  · rename_i accepted
    have small : t / 2 + 1 < Fintype.card V := by omega
    have pass := accepted.2.2
    have scheduled := accepted.2.1
    have no := false_short_pass G leader ell (t / 2 + 1) observer valid leaders accepted.1 small
    exact False.elim (no (scheduled ▸ pass))
  · rfl

theorem shortDecision_at (ell : ℕ) (observer : V) (valid : Admissible ell G leader)
    (nonleaders : ell < Fintype.card V) :
    shortDecision ell (2 * Fintype.card V - 2) (history G leader (2 * Fintype.card V - 2) observer) =
      some (Fintype.card V) := by
  classical
  have positive := valid.positive
  have candidate : (2 * Fintype.card V - 2) / 2 + 1 = Fintype.card V := by omega
  unfold shortDecision
  dsimp only
  rw [candidate, if_pos ⟨nonleaders, rfl, true_short_pass G leader ell observer valid nonleaders⟩]

theorem local_all_leaders_iff (ell : ℕ) (observer : V) (valid : Admissible ell G leader) :
    (false ∉ levels ell (history G leader ell observer) 0) ↔ Fintype.card V = ell := by
  classical
  have occurrence : false ∈ levels ell (history G leader ell observer) 0 ↔
      Sees (r := 0) false ell (history G leader (0 + ell) observer) := by
    unfold levels
    rw [dif_pos (Nat.zero_le ell), cast_history G leader ell (0 + (ell - 0)) (by omega) observer]
    change false ∈ occurrences 0 ell (history G leader (0 + ell) observer) ↔ _
    exact mem_occurrences 0 ell _ false
  exact (not_congr occurrence).trans (all_leaders_test_iff G leader ell valid observer)

theorem optimizedTime_positive (ell : ℕ) (valid : Admissible ell G leader) :
    0 < optimizedTime (Fintype.card V) ell := by
  have population := valid.leaderCount_le_card
  have positive := valid.positive
  unfold optimizedTime
  split_ifs <;> omega

theorem optimizedDecision_before (ell t : ℕ) (observer : V) (valid : Admissible ell G leader)
    (before : t < optimizedTime (Fintype.card V) ell) :
    optimizedDecision ell t (history G leader t observer) = none := by
  classical
  have population := valid.leaderCount_le_card
  have positive := valid.positive
  unfold optimizedDecision
  split
  · rename_i equal
    subst t
    rw [if_neg]
    intro absent
    have all := (local_all_leaders_iff G leader ell observer valid).mp absent
    simp only [optimizedTime, if_pos all] at before
    omega
  · split
    · apply coreDecision_before G leader ell t observer valid
      unfold optimizedTime at before
      split_ifs at before <;> omega
    · rename_i notOne
      apply shortDecision_before G leader ell t observer valid (by omega)
      unfold optimizedTime at before
      split_ifs at before <;> omega

theorem optimizedDecision_at (ell : ℕ) (observer : V) (valid : Admissible ell G leader) :
    optimizedDecision ell (optimizedTime (Fintype.card V) ell)
      (history G leader (optimizedTime (Fintype.card V) ell) observer) = some (Fintype.card V) := by
  classical
  have population := valid.leaderCount_le_card
  have positive := valid.positive
  by_cases all : Fintype.card V = ell
  · have stop : optimizedTime (Fintype.card V) ell = ell := by simp [optimizedTime, all]
    rw [stop]
    have absent := (local_all_leaders_iff G leader ell observer valid).mpr all
    simp only [optimizedDecision, if_pos absent]
    exact congrArg some all.symm
  · by_cases one : ell = 1
    · have stop : optimizedTime (Fintype.card V) ell = 2 * Fintype.card V - 1 := by
        unfold optimizedTime
        rw [if_neg all, if_pos one]
      rw [stop]
      have different : 2 * Fintype.card V - 1 ≠ ell := by omega
      simp only [optimizedDecision, if_neg different, if_pos one]
      exact coreDecision_at G leader ell observer valid
    · have stop : optimizedTime (Fintype.card V) ell = 2 * Fintype.card V - 2 := by
        unfold optimizedTime
        rw [if_neg all, if_neg one]
      rw [stop]
      have different : 2 * Fintype.card V - 2 ≠ ell := by omega
      simp only [optimizedDecision, if_neg different, if_neg one]
      exact shortDecision_at G leader ell observer valid (by omega)

/-- Core simultaneous termination, including an explicit proof that every
agent is active at every earlier round in the silent-halting model. -/
theorem core_simultaneous (ell : ℕ) (valid : Admissible ell G leader) :
    (∀ t, t < 2 * Fintype.card V - 1 → ∀ x,
      core.trace ell G leader t x = .active (pack t (history G leader t x))) ∧
    (∀ x, core.trace ell G leader (2 * Fintype.card V - 1) x =
      .halted (pack (2 * Fintype.card V - 1) (history G leader (2 * Fintype.card V - 1) x)) (Fintype.card V)) := by
  have positive : 0 < Fintype.card V := lt_of_lt_of_le valid.positive valid.leaderCount_le_card
  exact simultaneous_from_decisions G leader coreDecision ell (2 * Fintype.card V - 1) (Fintype.card V)
    (by omega) (fun t _ ht x => coreDecision_before G leader ell t x valid ht)
    (fun x => coreDecision_at G leader ell x valid)

/-- The optimized protocol has exactly the three scheduled simultaneous
halting times, with no earlier output and no earlier silent sender. -/
theorem optimized_simultaneous (ell : ℕ) (valid : Admissible ell G leader) :
    (∀ t, t < optimizedTime (Fintype.card V) ell → ∀ x,
      optimized.trace ell G leader t x = .active (pack t (history G leader t x))) ∧
    (∀ x, optimized.trace ell G leader (optimizedTime (Fintype.card V) ell) x =
      .halted (pack (optimizedTime (Fintype.card V) ell)
        (history G leader (optimizedTime (Fintype.card V) ell) x)) (Fintype.card V)) :=
  simultaneous_from_decisions G leader optimizedDecision ell (optimizedTime (Fintype.card V) ell) (Fintype.card V)
    (optimizedTime_positive G leader ell valid)
    (fun t _ ht x => optimizedDecision_before G leader ell t x valid ht)
    (fun x => optimizedDecision_at G leader ell x valid)

theorem core_halted_silent_forever (ell : ℕ) (valid : Admissible ell G leader) (d : ℕ) (x : V) :
    core.trace ell G leader (2 * Fintype.card V - 1 + d) x =
      .halted (pack (2 * Fintype.card V - 1) (history G leader (2 * Fintype.card V - 1) x)) (Fintype.card V) ∧
    (core.trace ell G leader (2 * Fintype.card V - 1 + d) x).message = none := by
  have forever := core.halted_forever ell G leader _ x _ _ ((core_simultaneous G leader ell valid).2 x) d
  exact ⟨forever, by rw [forever]; rfl⟩

theorem optimized_halted_silent_forever (ell : ℕ) (valid : Admissible ell G leader) (d : ℕ) (x : V) :
    optimized.trace ell G leader (optimizedTime (Fintype.card V) ell + d) x =
      .halted (pack (optimizedTime (Fintype.card V) ell)
        (history G leader (optimizedTime (Fintype.card V) ell) x)) (Fintype.card V) ∧
    (optimized.trace ell G leader (optimizedTime (Fintype.card V) ell + d) x).message = none := by
  have forever := optimized.halted_forever ell G leader _ x _ _ ((optimized_simultaneous G leader ell valid).2 x) d
  exact ⟨forever, by rw [forever]; rfl⟩

theorem core_solves_counting : core.SolvesCounting := by
  intro V _ ell G leader valid
  obtain ⟨active, halted⟩ := core_simultaneous G leader ell valid
  refine ⟨?_, ⟨2 * Fintype.card V - 1, fun x => ⟨_, halted x⟩⟩⟩
  intro t x s k hk
  by_cases before : t < 2 * Fintype.card V - 1
  · rw [active t before x] at hk
    cases hk
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt before)
    rw [(core_halted_silent_forever G leader ell valid d x).1] at hk
    cases hk
    rfl

theorem optimized_solves_counting : optimized.SolvesCounting := by
  intro V _ ell G leader valid
  obtain ⟨active, halted⟩ := optimized_simultaneous G leader ell valid
  refine ⟨?_, ⟨optimizedTime (Fintype.card V) ell, fun x => ⟨_, halted x⟩⟩⟩
  intro t x s k hk
  by_cases before : t < optimizedTime (Fintype.card V) ell
  · rw [active t before x] at hk
    cases hk
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt before)
    rw [(optimized_halted_silent_forever G leader ell valid d x).1] at hk
    cases hk
    rfl

end Counting.TimingProtocol
