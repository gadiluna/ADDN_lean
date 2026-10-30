import Counting.ExecutableRefinementProtocol

namespace Counting.Executable
open Counting.TimingProtocol

variable {V : Type} [Fintype V]
variable (G : Nat → V → V → Nat) (leader : V → Bool)

theorem executable_before (ell : Nat) (network : Counting.Admissible ell G leader) :
    ∀ depth, depth < optimizedTime (Fintype.card V) ell → ∀ receiver,
      ∃ state, StateRep ell depth (Counting.history G leader depth receiver) state ∧
        state.output = none ∧ executableProtocol.trace ell G leader depth receiver = .active state := by
  intro depth
  induction depth with
  | zero =>
      intro _ receiver
      exact ⟨initialState ell (leader receiver), initialState_rep ell (leader receiver), rfl, rfl⟩
  | succ depth ih =>
      intro before receiver
      have previous := ih (by omega)
      choose states represented active trace using previous
      obtain ⟨next, rep, output, step⟩ := executable_trace_step G leader ell depth network.positive
        states represented active trace receiver
      have none := optimizedDecision_before G leader ell (depth + 1) receiver network before
      rw [none] at output
      exact ⟨next, rep, output, by simpa only [output] using step⟩

/-- Every agent halts at the exact optimized time, with a valid compressed
DAG denoting its physical history and with the actual population as output. -/
theorem executable_at_stop (ell : Nat) (network : Counting.Admissible ell G leader) (receiver : V) :
    ∃ state, StateRep ell (optimizedTime (Fintype.card V) ell)
        (Counting.history G leader (optimizedTime (Fintype.card V) ell) receiver) state ∧
      state.output = some (Fintype.card V) ∧
      executableProtocol.trace ell G leader (optimizedTime (Fintype.card V) ell) receiver =
        .halted state (Fintype.card V) := by
  have positive := optimizedTime_positive G leader ell network
  obtain ⟨depth, stop⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt positive)
  have previous := executable_before G leader ell network depth (by omega)
  choose states represented active trace using previous
  obtain ⟨next, rep, output, step⟩ := executable_trace_step G leader ell depth network.positive
    states represented active trace receiver
  have atStop := optimizedDecision_at G leader ell receiver network
  rw [stop] at atStop
  rw [atStop] at output
  rw [stop]
  exact ⟨next, rep, output, by simpa only [output] using step⟩

/-- Simultaneous first halting for the program placed in the actual silent
protocol model. Every earlier sender is active; every later sender is silent. -/
theorem executable_simultaneous (ell : Nat) (network : Counting.Admissible ell G leader) :
    (∀ depth, depth < optimizedTime (Fintype.card V) ell → ∀ receiver,
      ∃ state, StateRep ell depth (Counting.history G leader depth receiver) state ∧
        state.output = none ∧ executableProtocol.trace ell G leader depth receiver = .active state) ∧
    (∀ receiver, ∃ state,
      StateRep ell (optimizedTime (Fintype.card V) ell)
        (Counting.history G leader (optimizedTime (Fintype.card V) ell) receiver) state ∧
      state.output = some (Fintype.card V) ∧
      executableProtocol.trace ell G leader (optimizedTime (Fintype.card V) ell) receiver =
        .halted state (Fintype.card V)) :=
  ⟨executable_before G leader ell network, executable_at_stop G leader ell network⟩

theorem executable_halted_silent_forever (ell : Nat) (network : Counting.Admissible ell G leader)
    (delay : Nat) (receiver : V) :
    ∃ state,
      executableProtocol.trace ell G leader (optimizedTime (Fintype.card V) ell + delay) receiver =
        .halted state (Fintype.card V) ∧
      (executableProtocol.trace ell G leader (optimizedTime (Fintype.card V) ell + delay) receiver).message = none := by
  obtain ⟨state, _, _, stopped⟩ := executable_at_stop G leader ell network receiver
  have forever := executableProtocol.halted_forever ell G leader _ receiver state _ stopped delay
  exact ⟨state, forever, by rw [forever]; rfl⟩

/-- Correct counting for every admissible finite population, using no
population size or agent identity in the executable local interface. -/
theorem executable_solves_counting : executableProtocol.SolvesCounting := by
  intro W _ ell graphs labels network
  refine ⟨?_, ⟨optimizedTime (Fintype.card W) ell, ?_⟩⟩
  · intro depth receiver state output halted
    by_cases before : depth < optimizedTime (Fintype.card W) ell
    · obtain ⟨_, _, _, active⟩ := executable_before graphs labels ell network depth before receiver
      rw [active] at halted
      cases halted
    · obtain ⟨delay, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt before)
      obtain ⟨_, forever, _⟩ := executable_halted_silent_forever graphs labels ell network delay receiver
      rw [forever] at halted
      cases halted
      rfl
  · intro receiver
    obtain ⟨state, _, _, stopped⟩ := executable_at_stop graphs labels ell network receiver
    exact ⟨state, stopped⟩

end Counting.Executable
