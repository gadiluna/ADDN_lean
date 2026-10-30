import Counting.EncodingNetwork
import Counting.DagSemanticsPhysical

namespace Counting.Encoding
open DirectedCounting

abbrev InputAgent (input : Simulation.Input) := Fin input.leaders.size

def inputLeader (input : Simulation.Input) (agent : InputAgent input) : Bool := input.leaders[agent.val]

def inputLeaderCount (input : Simulation.Input) : Nat :=
  (Finset.univ.filter (fun agent : InputAgent input => inputLeader input agent = true)).card

def matrixEdge (graph : Simulation.RoundGraph) (n : Nat) (a b : Fin n) : Nat :=
  ((graph[a.val]?.getD #[])[b.val]?.getD 0)

/-- The listed matrices are rounds 1,...,t; an explicit complete-graph
continuation makes the infinite semantic network total. -/
def inputGraph (input : Simulation.Input) (round : Nat) : InputAgent input → InputAgent input → Nat :=
  if 0 < round ∧ round ≤ input.rounds.size then
    matrixEdge (input.rounds[round-1]?.getD #[]) input.leaders.size
  else fun _ _ => 1

def matrixShape (n : Nat) (graph : Simulation.RoundGraph) : Bool :=
  graph.size == n && graph.all (fun row => row.size == n)

/-- Binary-input validation allows loops and parallel arcs, including the
zero-edge singleton. Unlike a node codec, it also checks the distributed
model's leader and round-connectivity requirements. -/
def networkValid (input : Simulation.Input) : Bool :=
  input.leaders.size > 0 && inputLeaderCount input > 0 &&
    (List.finRange input.rounds.size).all (fun r =>
      matrixShape input.leaders.size input.rounds[r.val] &&
      strongConnectivityCheck (fun a b : InputAgent input =>
        decide (0 < matrixEdge input.rounds[r.val] input.leaders.size a b)))

theorem input_leaderCount_eq (input : Simulation.Input) :
    Counting.leaderCount (inputLeader input) = inputLeaderCount input := rfl

theorem networkValid_iff (input : Simulation.Input) :
    networkValid input = true ↔
      0 < input.leaders.size ∧ 0 < inputLeaderCount input ∧
      ∀ r : Fin input.rounds.size,
        matrixShape input.leaders.size input.rounds[r.val] = true ∧
        StronglyConnected (fun a b : InputAgent input =>
          0 < matrixEdge input.rounds[r.val] input.leaders.size a b) := by
  simp only [networkValid, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_finRange, forall_true_left, strongConnectivityCheck_eq_true_iff]
  tauto

theorem inputGraph_listed (input : Simulation.Input) (r : Fin input.rounds.size) :
    inputGraph input (r.val+1) = matrixEdge input.rounds[r.val] input.leaders.size := by
  have within : 0 < r.val+1 ∧ r.val+1 ≤ input.rounds.size := by have := r.isLt; omega
  simp only [inputGraph, if_pos within, Nat.add_sub_cancel, Array.getElem?_eq_getElem r.isLt,
    Option.getD_some]

theorem networkValid_admissible (input : Simulation.Input) (valid : networkValid input = true) :
    Counting.Admissible (inputLeaderCount input) (inputGraph input) (inputLeader input) := by
  obtain ⟨_, positive, rounds⟩ := (networkValid_iff input).mp valid
  refine ⟨positive, input_leaderCount_eq input, ?_⟩
  intro round afterZero
  by_cases within : round ≤ input.rounds.size
  · let r : Fin input.rounds.size := ⟨round-1, by omega⟩
    have equal : r.val+1 = round := by dsimp [r]; omega
    rw [← equal, inputGraph_listed input r]
    exact (rounds r).2
  · simp only [inputGraph, within, and_false, if_false]
    intro a b
    exact Relation.ReflTransGen.single (by norm_num)

/-- Finite prefix semantics of the actual binary input. The observer is a
physical model parameter; it is never passed to the anonymous local updater. -/
noncomputable def inputHistory (input : Simulation.Input) (observer : InputAgent input) :
    Counting.FullHistory input.rounds.size :=
  Counting.history (inputGraph input) (inputLeader input) input.rounds.size observer

/-- The implemented shared-DAG updater produces precisely that input's
history at every observer, with validity maintained by real updates. -/
theorem input_vista_correct (input : Simulation.Input) (observer : InputAgent input) :
    let v := Executable.physicalVistaRun (inputGraph input) (inputLeader input) input.rounds.size observer
    v.valid = true ∧ (v.node v.bottom).level = input.rounds.size ∧
      Executable.decodeNode v input.rounds.size v.bottom = inputHistory input observer :=
  Executable.physical_vista_run_correct (inputGraph input) (inputLeader input) input.rounds.size observer

/-- Canonical parse plus model validation. Invalid binary encodings and
inadmissible matrices both give a negative boundary result. -/
def decodeNetwork? (bits : List Bool) : Option Simulation.Input :=
  match networkInput.decodeExact bits with
  | none => none
  | some input => if networkValid input then some input else none

theorem decodeNetwork_iff (bits : List Bool) (input : Simulation.Input) :
    decodeNetwork? bits = some input ↔ networkInput.encode input = bits ∧ networkValid input = true := by
  change (match networkInput.decodeExact bits with
    | none => none
    | some found => if networkValid found then some found else none) = some input ↔ _
  cases parsed : networkInput.decodeExact bits with
  | none =>
      simp only [reduceCtorEq, false_iff, not_and]
      intro encoding
      have exact := (networkInput.decodeExact_iff bits input).mpr encoding
      rw [parsed] at exact
      cases exact
  | some found =>
      by_cases valid : networkValid found = true
      · simp only [valid, if_true, Option.some.injEq]
        constructor
        · intro equal
          subst input
          exact ⟨(networkInput.decodeExact_iff bits found).mp parsed, valid⟩
        · rintro ⟨encoded, _⟩
          have equal := (networkInput.decodeExact_iff bits input).mpr encoded
          rw [parsed] at equal
          exact Option.some.inj equal
      · simp only [valid, if_false, reduceCtorEq, false_iff, not_and]
        intro encoded inputValid
        have equal := (networkInput.decodeExact_iff bits input).mpr encoded
        rw [parsed] at equal
        exact valid (Option.some.inj equal ▸ inputValid)

end Counting.Encoding
