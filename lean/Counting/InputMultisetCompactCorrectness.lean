import Counting.InputMultisetCompact
import Counting.InputMultisetDagCorrectness

/-!
# Unconditional correctness of the compact input-multiset implementation

Both channels and reconstruction use shared DAGs and binary multiplicities.
The semantic history expansions occur in proofs only. There is no unproved
reconstruction or solver-success premise in the public conclusions below.
-/

namespace Counting.InputMultiset.Compact
open Counting.Executable
open scoped BigOperators

variable {Input : Type} [DecidableEq Input] [Encodable Input] [Inhabited Input]

/-- Direct finite-node reconstruction; it never decodes a DAG into a tree. -/
def recover (n : Nat) (vista : Vista) : Option (Multiset Input) :=
  DagRecovery.recover n vista Dag.encodableInputOf

/-- The complete executable step for arbitrary serializable initial inputs. -/
def step (state : State Input) (received : List (Packet × Nat)) (outdegree : Nat) :
    Option (State Input) := advance? recover state received outdegree

variable {V : Type} [Fintype V]
variable (G : Nat → V → V → Nat) (leader : V → Bool) (input : V → Input) (ell : Nat)

noncomputable def execution : Nat → V → State Input :=
  run Encodable.encode recover G leader input ell

theorem recover_physical (valid : Admissible ell G leader)
    (t : Nat) (late : 2 * Fintype.card V - 2 ≤ t) (x : V) :
    recover (Fintype.card V) (Dag.physicalRun Encodable.encode G leader input t x) =
      some (Finset.univ.val.map input) := by
  have positive : 0 < Fintype.card V := lt_of_lt_of_le valid.positive valid.leaderCount_le_card
  letI : Nonempty V := Fintype.card_pos_iff.mp positive
  exact Dag.recoverDag_correct Encodable.encode Dag.encodableInputOf
    Dag.encodableInputOf_encode G leader input valid.connected t late x _
    (Dag.physicalRun_rep Encodable.encode G leader input t x)

/-- Every earlier round is active, and every agent returns the exact input
multiset at `max(T(n,ell),2n-2)` in the actual compact execution. -/
theorem executable_simultaneous (valid : Admissible ell G leader) :
    (∀ t, t < terminationTime (Fintype.card V) ell → ∀ x,
      (execution G leader input ell t x).output = none ∧
        (message (execution G leader input ell t x)).isSome = true) ∧
    (∀ x, (execution G leader input ell (terminationTime (Fintype.card V) ell) x).output =
      some (Finset.univ.val.map input)) := by
  constructor
  · intro t ht x
    have eq := run_before Encodable.encode recover G leader input ell valid t ht x
    change _ = none ∧ _ = true
    simp only [execution, eq, collected, message, Option.isSome_none, Bool.false_eq_true,
      ↓reduceIte, Option.isSome_some, and_self]
  · intro x
    have eq := run_at Encodable.encode recover G leader input ell valid
      (recover_physical G leader input ell valid) x
    simp only [execution, eq]

/-- All later states retain the exact answer and send no packets on either channel. -/
theorem executable_silent_after (valid : Admissible ell G leader) (delay : Nat) (x : V) :
    (execution G leader input ell (terminationTime (Fintype.card V) ell + delay) x).output =
      some (Finset.univ.val.map input) ∧
    message (execution G leader input ell (terminationTime (Fintype.card V) ell + delay) x) = none := by
  constructor
  · unfold execution
    rw [run_frozen Encodable.encode recover G leader input ell valid
      (recover_physical G leader input ell valid) delay x,
      run_at Encodable.encode recover G leader input ell valid
      (recover_physical G leader input ell valid) x]
  · exact silent_after Encodable.encode recover G leader input ell valid
      (recover_physical G leader input ell valid) delay x

/-- A valid execution never takes the error fallback, before or after stopping. -/
theorem executable_step_total (valid : Admissible ell G leader) (t : Nat) (x : V) :
    ∃ next, step (execution G leader input ell t x)
      (packets (G (t + 1)) (execution G leader input ell t) x)
      (∑ y, G (t + 1) x y) = some next :=
  run_step_total Encodable.encode recover G leader input ell valid
    (recover_physical G leader input ell valid) t x

/-- Safety and termination hold uniformly over all admissible populations;
the actual population and the initial assignment are absent from `step`. -/
theorem executable_solves_multiset :
    ∀ (W : Type) [Fintype W] (leaders : Nat) (graphs : Nat → W → W → Nat)
      (flags : W → Bool) (values : W → Input), Admissible leaders graphs flags →
      (∀ t x result, (execution graphs flags values leaders t x).output = some result →
        result = Finset.univ.val.map values) ∧
      (∀ x, (execution graphs flags values leaders
        (terminationTime (Fintype.card W) leaders) x).output = some (Finset.univ.val.map values)) := by
  intro W _ leaders graphs flags values valid
  refine ⟨?_, (executable_simultaneous graphs flags values leaders valid).2⟩
  intro t x result output
  by_cases before : t < terminationTime (Fintype.card W) leaders
  · rw [(executable_simultaneous graphs flags values leaders valid).1 t before x |>.1] at output
    cases output
  · obtain ⟨delay, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt before)
    rw [(executable_silent_after graphs flags values leaders valid delay x).1] at output
    exact (Option.some.inj output).symm

/-- In the cases `n > ell`, the implementation preserves the exact Counting
bound, not merely its asymptotic linear complexity. -/
theorem executable_same_counting_rounds (valid : Admissible ell G leader)
    (nonleaders : ell < Fintype.card V) :
    (∀ t, t < TimingProtocol.optimizedTime (Fintype.card V) ell → ∀ x,
      (execution G leader input ell t x).output = none) ∧
    (∀ x, (execution G leader input ell (TimingProtocol.optimizedTime (Fintype.card V) ell) x).output =
      some (Finset.univ.val.map input)) := by
  obtain ⟨before, stopped⟩ := executable_simultaneous G leader input ell valid
  rw [terminationTime_nonleaders _ _ valid.positive nonleaders] at before stopped
  exact ⟨fun t ht x => (before t ht x).1, stopped⟩

end Counting.InputMultiset.Compact
