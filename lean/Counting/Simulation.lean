import Counting.Executable
import DirectedCountingFormalization.StrongConnectivityCheck
import Lean.Data.Json

/-! A finite, globally indexed simulation harness. Indices and the population
occur only here; `Executable.advance?` receives its own state, a multiset of
messages, and its outdegree. This module does not assert protocol correctness.
The JSON boundary validates every supplied graph before any round is executed.
-/
namespace Counting.Simulation

open Counting.Executable Lean

abbrev RoundGraph := Array (Array Nat)

/-- A sender contributes its preceding vista once, with the binary multiplicity
of its arc bundle. Halted senders contribute no messages. -/
def networkRound (graph : RoundGraph) (states : Array LocalState) :
    Option (Array LocalState) := do
  let mut result := #[]
  for x in List.range states.size do
    let state ← states[x]?
    let outgoing ← graph[x]?
    let mut received := []
    for y in List.range states.size do
      let sender ← states[y]?
      let row ← graph[y]?
      let count ← row[x]?
      if sender.output.isNone && count > 0 then
        received := (sender.vista, count) :: received
    let next ← advance? state received outgoing.toList.sum
    result := result.push next
  return result

def repeatRounds (graph : RoundGraph) :
    Nat → Array LocalState → Option (Array LocalState)
  | 0, states => some states
  | rounds + 1, states => do
      let next ← networkRound graph states
      repeatRounds graph rounds next

def initialNetwork (leaders : Nat) (statuses : List Bool) : Array LocalState :=
  (statuses.map (initialState leaders)).toArray

structure Input where
  leaders : Array Bool
  rounds : Array RoundGraph
deriving Repr, BEq, DecidableEq

def Input.leaderCount (input : Input) : Nat :=
  (input.leaders.filter id).size

/-- Reachability uses reflexive paths, so a singleton with zero arcs is valid.
Loops and parallel arcs are allowed. Dimensions are checked separately. -/
def graphStronglyConnected (graph : RoundGraph) : Bool :=
  DirectedCounting.strongConnectivityCheck
    (fun i j : Fin graph.size => 0 < ((graph[i.val]?.getD #[])[j.val]?.getD 0))

def Input.validate (input : Input) : Except String Unit := do
  let n := input.leaders.size
  if n == 0 then throw "leaders: the population must be nonempty"
  if input.leaderCount == 0 then throw "leaders: at least one leader is required"
  for t in List.range input.rounds.size do
    let graph := input.rounds[t]!
    if graph.size != n then
      throw s!"rounds[{t}]: expected {n} rows, got {graph.size}"
    for i in List.range n do
      let row := graph[i]!
      if row.size != n then
        throw s!"rounds[{t}][{i}]: expected {n} columns, got {row.size}"
    if !graphStronglyConnected graph then
      throw s!"rounds[{t}]: the directed graph is not strongly connected"

private def atField {α : Type} (field : String) (result : Except String α) :
    Except String α := result.mapError (fun error => s!"{field}: {error}")

def Input.fromJson (json : Json) : Except String Input := do
  let leaderJson ← json.getObjVal? "leaders"
  let leaderArray ← atField "leaders" leaderJson.getArr?
  let mut leaders := #[]
  for i in List.range leaderArray.size do
    let leader ← atField s!"leaders[{i}]" (leaderArray[i]!.getBool?)
    leaders := leaders.push leader
  let roundsJson ← json.getObjVal? "rounds"
  let roundsArray ← atField "rounds" roundsJson.getArr?
  let mut rounds := #[]
  for t in List.range roundsArray.size do
    let rows ← atField s!"rounds[{t}]" (roundsArray[t]!.getArr?)
    let mut graph := #[]
    for i in List.range rows.size do
      let entries ← atField s!"rounds[{t}][{i}]" (rows[i]!.getArr?)
      let mut row := #[]
      for j in List.range entries.size do
        let count ← atField s!"rounds[{t}][{i}][{j}]" (entries[j]!.getNat?)
        row := row.push count
      graph := graph.push row
    rounds := rounds.push graph
  let input : Input := ⟨leaders, rounds⟩
  input.validate
  return input

def Input.parse (text : String) : Except String Input := do
  Input.fromJson (← Json.parse text)

def statesJson (states : Array LocalState) : Json :=
  Json.arr (states.mapIdx fun i state =>
    Json.mkObj [
      ("agent", toJson i),
      ("output", toJson state.output),
      ("vista_depth", toJson (state.vista.node state.vista.bottom).level),
      ("dag_nodes", toJson state.vista.nodes.size),
      ("dag_valid", toJson state.vista.valid)])

def roundJson (round : Nat) (states : Array LocalState) : Json :=
  Json.mkObj [("round", toJson round),
    ("all_halted", toJson (states.all fun state => state.output.isSome)),
    ("agents", statesJson states)]

/-- Execute precisely the supplied finite prefix, including snapshots of frozen
states after halting. A prefix ending before halting is a successful simulation.
Input is validated here too, so callers need not use the JSON decoder. -/
def simulate (input : Input) : Except String Json := do
  input.validate
  let mut states := initialNetwork input.leaderCount input.leaders.toList
  let mut trace := #[roundJson 0 states]
  for t in List.range input.rounds.size do
    let some next := networkRound input.rounds[t]! states
      | throw s!"round {t+1}: the executable local transition rejected its input"
    states := next
    trace := trace.push (roundJson (t+1) states)
  return Json.mkObj [
    ("population", toJson input.leaders.size),
    ("leader_count", toJson input.leaderCount),
    ("rounds_executed", toJson input.rounds.size),
    ("all_halted", toJson (states.all fun state => state.output.isSome)),
    ("trace", Json.arr trace)]

end Counting.Simulation
