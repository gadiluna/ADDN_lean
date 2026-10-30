import Counting.InputMultisetCounting
import Counting.InputMultisetLocalCorrectness
import Counting.InputProtocolPostprocess

/-!
# Input-multiset computation at the Counting round bound

The reconstruction theorem is discharged here for the actual local finite
search. There is no assumption of a successful solver, correct inferred
population, visible complete level, or knowledge of identities. Those facts
are proved from the admissible network and the local Counting execution.
-/

namespace Counting.InputMultiset
open Counting.InputProtocol

variable {Input : Type} [DecidableEq Input]

/-- The local input-multiset algorithm runs the certified Counting program and
retains input information until population-normalized reconstruction is ready. -/
noncomputable def algorithm : InputProtocol.Protocol Input (Multiset Input) (State Input) :=
  protocol InputMultisetLocal.recover

variable {V : Type} [Fintype V]
variable (G : Nat → V → V → Nat) (leader : V → Bool) (input : V → Input) (ell : Nat)

/-- Unconditional first simultaneous termination at `max(T(n,ell), 2n-2)`.
The input multiset is exact, including repetitions. -/
theorem algorithm_simultaneous (valid : Admissible ell G leader) :
    (∀ t, t < terminationTime (Fintype.card V) ell → ∀ x,
      algorithm.trace ell G leader input t x =
        .active (physicalState G leader input ell t x)) ∧
    (∀ x, algorithm.trace ell G leader input (terminationTime (Fintype.card V) ell) x =
      .halted (physicalState G leader input ell (terminationTime (Fintype.card V) ell) x)
        (Finset.univ.val.map input)) := by
  have positive : 0 < Fintype.card V := lt_of_lt_of_le valid.positive valid.leaderCount_le_card
  letI : Nonempty V := Fintype.card_pos_iff.mp positive
  exact simultaneous G leader input ell InputMultisetLocal.recover valid
    (fun t late x => InputMultisetLocal.recover_correct G leader input valid.connected t late x)

theorem algorithm_silent_after (valid : Admissible ell G leader) (delay : Nat) (x : V) :
    algorithm.trace ell G leader input (terminationTime (Fintype.card V) ell + delay) x =
      .halted (physicalState G leader input ell (terminationTime (Fintype.card V) ell) x)
        (Finset.univ.val.map input) ∧
    (algorithm.trace ell G leader input
      (terminationTime (Fintype.card V) ell + delay) x).message = none := by
  have forever := algorithm.halted_forever ell G leader input _ x _ _
    ((algorithm_simultaneous G leader input ell valid).2 x) delay
  exact ⟨forever, by rw [forever]; rfl⟩

/-- One local protocol solves input-multiset computation for every admissible
population, every leader assignment and every assignment of initial inputs. -/
theorem algorithm_solves_multiset :
    ∀ (W : Type) [Fintype W] (leaders : Nat) (graphs : Nat → W → W → Nat)
      (flags : W → Bool) (values : W → Input), Admissible leaders graphs flags →
      (∀ t x s result, algorithm.trace leaders graphs flags values t x = .halted s result →
        result = Finset.univ.val.map values) ∧
      (∃ t, ∀ x, ∃ s, algorithm.trace leaders graphs flags values t x =
        .halted s (Finset.univ.val.map values)) := by
  intro W _ leaders graphs flags values valid
  refine ⟨?_, ⟨terminationTime (Fintype.card W) leaders, ?_⟩⟩
  · intro t x s result halted
    by_cases before : t < terminationTime (Fintype.card W) leaders
    · rw [(algorithm_simultaneous graphs flags values leaders valid).1 t before x] at halted
      cases halted
    · obtain ⟨delay, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt before)
      rw [(algorithm_silent_after graphs flags values leaders valid delay x).1] at halted
      cases halted
      rfl
  · intro x
    exact ⟨_, (algorithm_simultaneous graphs flags values leaders valid).2 x⟩

/-- With at least one nonleader, multiset computation preserves exactly the
already certified Counting schedule, for both one and multiple leaders. -/
theorem algorithm_same_counting_rounds (valid : Admissible ell G leader)
    (nonleaders : ell < Fintype.card V) :
    (∀ t, t < TimingProtocol.optimizedTime (Fintype.card V) ell → ∀ x,
      algorithm.trace ell G leader input t x = .active (physicalState G leader input ell t x)) ∧
    (∀ x, algorithm.trace ell G leader input (TimingProtocol.optimizedTime (Fintype.card V) ell) x =
      .halted (physicalState G leader input ell (TimingProtocol.optimizedTime (Fintype.card V) ell) x)
        (Finset.univ.val.map input)) := by
  simpa only [terminationTime_nonleaders _ _ valid.positive nonleaders] using
    algorithm_simultaneous G leader input ell valid

/-- Apply any given local function to the recovered multiset at the same
round. If that function is computable, this postprocessing is computable too;
there are no extra communication rounds. -/
theorem function_simultaneous {Output : Type} (f : Multiset Input → Output)
    (valid : Admissible ell G leader) :
    (∀ t, t < terminationTime (Fintype.card V) ell → ∀ x,
      (algorithm.mapOutput f).trace ell G leader input t x =
        .active (physicalState G leader input ell t x)) ∧
    (∀ x, (algorithm.mapOutput f).trace ell G leader input (terminationTime (Fintype.card V) ell) x =
      .halted (physicalState G leader input ell (terminationTime (Fintype.card V) ell) x)
        (f (Finset.univ.val.map input))) := by
  obtain ⟨before, stopped⟩ := algorithm_simultaneous G leader input ell valid
  constructor
  · intro t ht x
    rw [InputProtocol.Protocol.trace_mapOutput, before t ht x]
    rfl
  · intro x
    rw [InputProtocol.Protocol.trace_mapOutput, stopped x]
    rfl

end Counting.InputMultiset
