import Counting.ExecutableRefinementCore

namespace Counting.Executable
open Counting.TimingProtocol

variable {V : Type} [Fintype V]
variable (G : Nat → V → V → Nat) (leader : V → Bool)

theorem executableCore_before (ell : Nat) (network : Counting.Admissible ell G leader) :
    ∀ depth, depth < (2 * Fintype.card V - 1) → ∀ receiver,
      ∃ state, StateRep ell depth (Counting.history G leader depth receiver) state ∧
        state.output = none ∧ executableCoreProtocol.trace ell G leader depth receiver = .active state := by
  intro depth
  induction depth with
  | zero =>
      intro _ receiver
      exact ⟨initialState ell (leader receiver), initialState_rep ell (leader receiver), rfl, rfl⟩
  | succ depth ih =>
      intro before receiver
      have previous := ih (by omega)
      choose states represented active trace using previous
      obtain ⟨next, rep, output, step⟩ := core_trace_step G leader ell depth network.positive
        states represented active trace receiver
      have none := coreDecision_before G leader ell (depth + 1) receiver network before
      rw [none] at output
      exact ⟨next, rep, output, by simpa only [output] using step⟩

/-- Every agent halts at the exact core time 2n−1, with a valid compressed
DAG denoting its physical history and with the actual population as output. -/
theorem executableCore_at_stop (ell : Nat) (network : Counting.Admissible ell G leader) (receiver : V) :
    ∃ state, StateRep ell ((2 * Fintype.card V - 1))
        (Counting.history G leader ((2 * Fintype.card V - 1)) receiver) state ∧
      state.output = some (Fintype.card V) ∧
      executableCoreProtocol.trace ell G leader ((2 * Fintype.card V - 1)) receiver =
        .halted state (Fintype.card V) := by
  have population : 0 < Fintype.card V := lt_of_lt_of_le network.positive network.leaderCount_le_card
  have positive : 0 < 2 * Fintype.card V - 1 := by omega
  obtain ⟨depth, stop⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt positive)
  have previous := executableCore_before G leader ell network depth (by omega)
  choose states represented active trace using previous
  obtain ⟨next, rep, output, step⟩ := core_trace_step G leader ell depth network.positive
    states represented active trace receiver
  have atStop := coreDecision_at G leader ell receiver network
  rw [stop] at atStop
  rw [atStop] at output
  rw [stop]
  exact ⟨next, rep, output, by simpa only [output] using step⟩

/-- Simultaneous first halting for the program placed in the actual silent
protocol model. Every earlier sender is active; every later sender is silent. -/
theorem executableCore_simultaneous (ell : Nat) (network : Counting.Admissible ell G leader) :
    (∀ depth, depth < (2 * Fintype.card V - 1) → ∀ receiver,
      ∃ state, StateRep ell depth (Counting.history G leader depth receiver) state ∧
        state.output = none ∧ executableCoreProtocol.trace ell G leader depth receiver = .active state) ∧
    (∀ receiver, ∃ state,
      StateRep ell ((2 * Fintype.card V - 1))
        (Counting.history G leader ((2 * Fintype.card V - 1)) receiver) state ∧
      state.output = some (Fintype.card V) ∧
      executableCoreProtocol.trace ell G leader ((2 * Fintype.card V - 1)) receiver =
        .halted state (Fintype.card V)) :=
  ⟨executableCore_before G leader ell network, executableCore_at_stop G leader ell network⟩

theorem executableCore_halted_silent_forever (ell : Nat) (network : Counting.Admissible ell G leader)
    (delay : Nat) (receiver : V) :
    ∃ state,
      executableCoreProtocol.trace ell G leader ((2 * Fintype.card V - 1) + delay) receiver =
        .halted state (Fintype.card V) ∧
      (executableCoreProtocol.trace ell G leader ((2 * Fintype.card V - 1) + delay) receiver).message = none := by
  obtain ⟨state, _, _, stopped⟩ := executableCore_at_stop G leader ell network receiver
  have forever := executableCoreProtocol.halted_forever ell G leader _ receiver state _ stopped delay
  exact ⟨state, forever, by rw [forever]; rfl⟩

/-- Correct counting for every admissible finite population, using no
population size or agent identity in the executable local interface. -/
theorem executableCore_solves_counting : executableCoreProtocol.SolvesCounting := by
  intro W _ ell graphs labels network
  refine ⟨?_, ⟨(2 * Fintype.card W - 1), ?_⟩⟩
  · intro depth receiver state output halted
    by_cases before : depth < (2 * Fintype.card W - 1)
    · obtain ⟨_, _, _, active⟩ := executableCore_before graphs labels ell network depth before receiver
      rw [active] at halted
      cases halted
    · obtain ⟨delay, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt before)
      obtain ⟨_, forever, _⟩ := executableCore_halted_silent_forever graphs labels ell network delay receiver
      rw [forever] at halted
      cases halted
      rfl
  · intro receiver
    obtain ⟨state, _, _, stopped⟩ := executableCore_at_stop graphs labels ell network receiver
    exact ⟨state, stopped⟩

end Counting.Executable
