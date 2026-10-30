import Counting.InputMultisetDag
import Counting.InputMultisetCounting
import Counting.ExecutableRefinementPhysical

/-! Executable compact two-channel implementation. The local transition takes
only its old state, binary message bundles, and the newly learned outdegree. -/

namespace Counting.InputMultiset.Compact
open Counting.Executable
open scoped BigOperators

structure State (Input : Type) where
  counting : LocalState
  vista : Vista
  output : Option (Multiset Input)

structure Packet where
  counting : Option Vista
  vista : Vista

def initial {Input : Type} (encode : Input → Nat) (ell : Nat) (leader : Bool) (input : Input) :
    State Input := ⟨initialState ell leader, Dag.initial encode leader input, none⟩

def message {Input : Type} (state : State Input) : Option Packet :=
  if state.output.isSome then none else
    some ⟨if state.counting.output.isNone then some state.counting.vista else none, state.vista⟩

def inputBundles (received : List (Packet × Nat)) : List (Vista × Nat) :=
  received.map (fun p => (p.1.vista, p.2))

def countingBundles (received : List (Packet × Nat)) : List (Vista × Nat) :=
  received.filterMap (fun p => p.1.counting.map (fun v => (v, p.2)))

def decideOutput {Input : Type} (recover : Nat → Vista → Option (Multiset Input))
    (counting : LocalState) (vista : Vista) : Option (Multiset Input) :=
  match counting.output with
  | none => none
  | some n => if 2 * n - 2 ≤ (vista.node vista.bottom).level - 1 then recover n vista else none

/-- This is the full local program, with no expansion of message multiplicities. -/
def advance? {Input : Type} (recover : Nat → Vista → Option (Multiset Input))
    (state : State Input) (received : List (Packet × Nat)) (degree : Nat) : Option (State Input) :=
  if state.output.isSome then some state else do
    let counting ← Executable.advance? state.counting (countingBundles received) degree
    let vista ← updateVista? state.vista (inputBundles received) degree
    return ⟨counting, vista, decideOutput recover counting vista⟩

def senderPackets {V Input : Type} (senders : List V) (edge : V → V → Nat)
    (states : V → State Input) (receiver : V) : List (Packet × Nat) :=
  senders.filterMap (fun sender => if edge sender receiver = 0 then none else
    (message (states sender)).map (fun packet => (packet, edge sender receiver)))

noncomputable def packets {V Input : Type} [Fintype V] (edge : V → V → Nat)
    (states : V → State Input) (receiver : V) : List (Packet × Nat) :=
  senderPackets Finset.univ.toList edge states receiver

theorem inputBundles_senderPackets {V Input : Type} (senders : List V)
    (edge : V → V → Nat) (states : V → State Input) (active : ∀ x, (states x).output = none)
    (receiver : V) :
    inputBundles (senderPackets senders edge states receiver) =
      senderBundles senders edge (fun x => (states x).vista) receiver := by
  induction senders with
  | nil => rfl
  | cons x xs ih =>
    by_cases edgeZero : edge x receiver = 0
    · simp [senderPackets, senderBundles, inputBundles, message, active, edgeZero] at *
      exact ih
    · simpa [senderPackets, senderBundles, inputBundles, message, active, edgeZero] using
        congrArg (fun rest => ((states x).vista, edge x receiver) :: rest) ih

theorem countingBundles_senderPackets {V Input : Type} (senders : List V)
    (edge : V → V → Nat) (states : V → State Input) (active : ∀ x, (states x).output = none)
    (receiver : V) :
    countingBundles (senderPackets senders edge states receiver) =
      senderBundles (senders.filter (fun x => (states x).counting.output.isNone)) edge
        (fun x => (states x).counting.vista) receiver := by
  induction senders with
  | nil => rfl
  | cons x xs ih =>
    cases ho : (states x).counting.output <;> by_cases he : edge x receiver = 0 <;>
      simp [senderPackets, senderBundles, countingBundles, message, active, ho, he] at *
    all_goals exact ih

variable {Input V : Type} [Fintype V]
variable (encode : Input → Nat) (recover : Nat → Vista → Option (Multiset Input))
variable (G : Nat → V → V → Nat) (leader : V → Bool) (input : V → Input) (ell : Nat)

noncomputable def collected (t : Nat) (x : V) : State Input :=
  ⟨binaryNetworkRun G leader ell t x, Dag.physicalRun encode G leader input t x, none⟩

theorem advance_collected (valid : Admissible ell G leader) (t : Nat) (x : V) :
    advance? recover (collected encode G leader input ell t x)
      (packets (G (t + 1)) (collected encode G leader input ell t) x)
      (∑ y, G (t + 1) x y) =
    some { collected encode G leader input ell (t + 1) x with
      output := decideOutput recover (binaryNetworkRun G leader ell (t + 1) x)
        (Dag.physicalRun encode G leader input (t + 1) x) } := by
  have inputEq := inputBundles_senderPackets Finset.univ.toList (G (t + 1))
    (collected encode G leader input ell t) (fun _ => rfl) x
  have countEq := countingBundles_senderPackets Finset.univ.toList (G (t + 1))
    (collected encode G leader input ell t) (fun _ => rfl) x
  obtain ⟨countNext, hc⟩ := binary_network_step_total G leader ell valid t x
  obtain ⟨inputNext, hi⟩ := Dag.physicalRun_step_total encode G leader input t x
  unfold packets at *
  simp only [advance?, collected, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
  rw [inputEq, countEq]
  change (do
      let c ← Executable.advance? (binaryNetworkRun G leader ell t x)
        (activePhysicalBundles (G (t + 1)) (binaryNetworkRun G leader ell t) x) _
      let v ← updateVista? (Dag.physicalRun encode G leader input t x)
        (physicalBundles (G (t + 1)) (Dag.physicalRun encode G leader input t) x) _
      pure (⟨c, v, decideOutput recover c v⟩ : State Input)) = _
  simp only [hc, hi, pure, binaryNetworkRun, Dag.physicalRun,
    Option.getD_some]
  rfl

/-- Actual execution freezes and suppresses all packets after the outer output. -/
noncomputable def run : Nat → V → State Input
  | 0, x => initial encode ell (leader x) (input x)
  | t + 1, x =>
      let previous := run t
      (advance? recover (previous x) (packets (G (t + 1)) previous x)
        (∑ y, G (t + 1) x y)).getD (previous x)

theorem decide_before (valid : Admissible ell G leader) (t : Nat)
    (before : t < terminationTime (Fintype.card V) ell) (x : V) :
    decideOutput recover (binaryNetworkRun G leader ell t x)
      (Dag.physicalRun encode G leader input t x) = none := by
  have level := (Dag.physicalRun_rep encode G leader input t x).level
  by_cases hc : t < TimingProtocol.optimizedTime (Fintype.card V) ell
  · simp only [decideOutput, (binary_network_before G leader ell valid t hc x).2]
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt hc)
    have short : TimingProtocol.optimizedTime (Fintype.card V) ell + d < 2 * Fintype.card V - 2 := by
      unfold terminationTime at before
      omega
    rw [binary_network_frozen G leader ell valid d x]
    simp only [decideOutput, (binary_network_at_stop G leader ell valid x).2, level,
      Nat.add_sub_cancel, if_neg (Nat.not_le.mpr short)]

theorem run_before (valid : Admissible ell G leader) :
    ∀ t, t < terminationTime (Fintype.card V) ell → ∀ x,
      run encode recover G leader input ell t x = collected encode G leader input ell t x := by
  intro t
  induction t with
  | zero => intro _ x; rfl
  | succ t ih =>
    intro ht x
    have states := funext (ih (by omega))
    rw [run, states, advance_collected encode recover G leader input ell valid,
      decide_before encode recover G leader input ell valid (t + 1) ht x]
    rfl

theorem decide_at (valid : Admissible ell G leader)
    (correct : ∀ t, 2 * Fintype.card V - 2 ≤ t → ∀ x,
      recover (Fintype.card V) (Dag.physicalRun encode G leader input t x) =
        some (Finset.univ.val.map input)) (x : V) :
    decideOutput recover
      (binaryNetworkRun G leader ell (terminationTime (Fintype.card V) ell) x)
      (Dag.physicalRun encode G leader input (terminationTime (Fintype.card V) ell) x) =
      some (Finset.univ.val.map input) := by
  have hc : TimingProtocol.optimizedTime (Fintype.card V) ell ≤
      terminationTime (Fintype.card V) ell := Nat.le_max_left _ _
  have ht : 2 * Fintype.card V - 2 ≤ terminationTime (Fintype.card V) ell := Nat.le_max_right _ _
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hc
  have frozen := binary_network_frozen G leader ell valid d x
  rw [← hd] at frozen
  have level := (Dag.physicalRun_rep encode G leader input (terminationTime (Fintype.card V) ell) x).level
  simp only [decideOutput, frozen, (binary_network_at_stop G leader ell valid x).2, level,
    Nat.add_sub_cancel, if_pos ht]
  exact correct _ ht x

theorem run_at (valid : Admissible ell G leader)
    (correct : ∀ t, 2 * Fintype.card V - 2 ≤ t → ∀ x,
      recover (Fintype.card V) (Dag.physicalRun encode G leader input t x) =
        some (Finset.univ.val.map input)) (x : V) :
    run encode recover G leader input ell (terminationTime (Fintype.card V) ell) x =
      { collected encode G leader input ell (terminationTime (Fintype.card V) ell) x with
        output := some (Finset.univ.val.map input) } := by
  have positive : 0 < terminationTime (Fintype.card V) ell :=
    lt_of_lt_of_le (TimingProtocol.optimizedTime_positive G leader ell valid) (Nat.le_max_left _ _)
  obtain ⟨t, ht⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt positive)
  have states := funext (run_before encode recover G leader input ell valid t (by omega))
  rw [ht, run, states, advance_collected encode recover G leader input ell valid]
  have output := decide_at encode recover G leader input ell valid correct x
  rw [ht] at output
  rw [output]
  rfl

theorem run_frozen (valid : Admissible ell G leader)
    (correct : ∀ t, 2 * Fintype.card V - 2 ≤ t → ∀ x,
      recover (Fintype.card V) (Dag.physicalRun encode G leader input t x) =
        some (Finset.univ.val.map input)) (delay : Nat) (x : V) :
    run encode recover G leader input ell (terminationTime (Fintype.card V) ell + delay) x =
      run encode recover G leader input ell (terminationTime (Fintype.card V) ell) x := by
  induction delay with
  | zero => rfl
  | succ delay ih =>
    rw [Nat.add_succ, run, ih, run_at encode recover G leader input ell valid correct x]
    simp only [advance?, Option.isSome_some, ↓reduceIte, Option.getD_some]

theorem silent_after (valid : Admissible ell G leader)
    (correct : ∀ t, 2 * Fintype.card V - 2 ≤ t → ∀ x,
      recover (Fintype.card V) (Dag.physicalRun encode G leader input t x) =
        some (Finset.univ.val.map input)) (delay : Nat) (x : V) :
    message (run encode recover G leader input ell
      (terminationTime (Fintype.card V) ell + delay) x) = none := by
  rw [run_frozen encode recover G leader input ell valid correct delay x,
    run_at encode recover G leader input ell valid correct x]
  rfl

/-- The error fallback of the global harness is unreachable at every round. -/
theorem run_step_total (valid : Admissible ell G leader)
    (correct : ∀ t, 2 * Fintype.card V - 2 ≤ t → ∀ x,
      recover (Fintype.card V) (Dag.physicalRun encode G leader input t x) =
        some (Finset.univ.val.map input)) (t : Nat) (x : V) :
    ∃ next, advance? recover (run encode recover G leader input ell t x)
      (packets (G (t + 1)) (run encode recover G leader input ell t) x)
      (∑ y, G (t + 1) x y) = some next := by
  by_cases before : t < terminationTime (Fintype.card V) ell
  · have states := funext (run_before encode recover G leader input ell valid t before)
    rw [states]
    exact ⟨_, advance_collected encode recover G leader input ell valid t x⟩
  · obtain ⟨delay, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt before)
    rw [run_frozen encode recover G leader input ell valid correct delay x,
      run_at encode recover G leader input ell valid correct x]
    exact ⟨_, rfl⟩

end Counting.InputMultiset.Compact
