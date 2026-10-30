import Counting.Simulation

/-! Executed regression tests, not substitutes for general correctness proofs.
No native decision axiom is used: tests are ordinary `#eval` programs.
-/
namespace Counting.Executable.Tests

private def require (name : String) (ok : Bool) : IO Unit :=
  unless ok do throw (IO.userError s!"Executable test failed: {name}")

open Counting.Simulation

def runBoundTest (name : String) (graph : Array (Array Nat))
    (leaders : Nat) (statuses : List Bool) (bound : Nat) : IO Unit := do
  let start := initialNetwork leaders statuses
  let some before := repeatRounds graph (bound - 1) start
    | throw (IO.userError s!"{name}: malformed execution before bound")
  require (name ++ ": no premature output") (before.all fun s => s.output.isNone)
  let some final := networkRound graph before
    | throw (IO.userError s!"{name}: malformed final execution")
  require (name ++ ": exact simultaneous output")
    (final.all fun s => s.output == some statuses.length)
  require (name ++ ": final DAG valid") (final.all fun s => s.vista.valid)
  require (name ++ ": linear nodes per level")
    (final.all fun s => s.vista.nodes.size ≤ statuses.length * (bound + 1))
  let some frozen := networkRound graph final
    | throw (IO.userError s!"{name}: halted state failed")
  require (name ++ ": halted states freeze") (frozen == final)

/-- Every generated round contains a directed spanning cycle. Additional arcs,
loops and binary bundle sizes vary deterministically from round to round. -/
def varyingGraph (order round : Nat) : Array (Array Nat) :=
  ((List.range order).map (fun x =>
    ((List.range order).map (fun y =>
      (if y == (x + 1) % order then 1 + (round + x) % 3 else 0) +
      (if (round + 2*x + 3*y) % 5 == 0 then round + 1 else 0))).toArray)).toArray

def runVaryingTest (order leaders : Nat) : IO Unit := do
  let bound := if order == leaders then order else if leaders == 1 then 2*order-1
    else 2*order-2
  let mut states := initialNetwork leaders ((List.range order).map (fun i => i < leaders))
  for round in List.range bound do
    require s!"varying n={order}, ell={leaders}: no early halt at {round}"
      (states.all fun s => s.output.isNone)
    let some next := networkRound (varyingGraph order (round+1)) states
      | throw (IO.userError s!"varying n={order}, ell={leaders}: invalid transition")
    require s!"varying n={order}, ell={leaders}: valid DAG at {round+1}"
      (next.all fun s => s.vista.valid)
    states := next
  require s!"varying n={order}, ell={leaders}: simultaneous halt at {bound}"
    (states.all fun s => s.output == some order)

def tests : IO Unit := do
  require "JSON singleton zero arcs accepted"
    (Input.parse "{\"leaders\":[true],\"rounds\":[[[0]]]}").isOk
  require "JSON empty graph prefix accepted"
    (Input.parse "{\"leaders\":[true,false],\"rounds\":[]}").isOk
  require "JSON empty population rejected"
    (!(Input.parse "{\"leaders\":[],\"rounds\":[]}").isOk)
  require "JSON no leaders rejected"
    (!(Input.parse "{\"leaders\":[false],\"rounds\":[[[0]]]}").isOk)
  require "JSON non-square graph rejected"
    (!(Input.parse "{\"leaders\":[true],\"rounds\":[[[0,1]]]}").isOk)
  require "JSON disconnected graph rejected"
    (!(Input.parse "{\"leaders\":[true,false],\"rounds\":[[[1,0],[0,1]]]}").isOk)
  require "JSON negative multiplicity rejected"
    (!(Input.parse "{\"leaders\":[true],\"rounds\":[[[-1]]]}").isOk)
  require "JSON fractional multiplicity rejected"
    (!(Input.parse "{\"leaders\":[true],\"rounds\":[[[0.5]]]}").isOk)
  require "JSON non-Boolean leader rejected"
    (!(Input.parse "{\"leaders\":[1],\"rounds\":[[[0]]]}").isOk)
  require "JSON missing rounds rejected" (!(Input.parse "{\"leaders\":[true]}").isOk)
  require "JSON large binary multiplicity accepted"
    (Input.parse
      "{\"leaders\":[true],\"rounds\":[[[1267650600228229401496703205376]]]}").isOk
  require "zero leaders has no schedule" ((candidateAt 0 5).isNone)
  require "one leader candidate schedule" (candidateAt 1 3 == some (2,2))
  require "multi leader candidate schedule" (candidateAt 2 4 == some (3,2))
  require "multi leader skips odd round" ((candidateAt 2 5).isNone)
  require "initial vista is valid" (initialVista true).valid
  require "empty vista rejected" (!((⟨#[], 0⟩ : Vista).valid))
  require "self-parent rejected"
    (!((⟨#[⟨1, some 0, true, 0, []⟩], 0⟩ : Vista).valid))
  require "zero received multiplicity rejected"
    ((updateVista? (initialVista true) [(initialVista false, 0)] 1).isNone)
  let some incomplete := updateVista? (initialVista true) [(initialVista false, 1)] 1
    | throw (IO.userError "incomplete-child fixture failed to update")
  require "incomplete visible-child fixture is a valid vista"
    (incomplete.valid && (levelNodes incomplete 0).any
      (fun node => (children incomplete node 1).isEmpty))
  require "audit rejects a visible node with no visible child"
    ((audit? incomplete 1 2 1).isNone)
  let complete3 := #[#[1,1,1],#[1,1,1],#[1,1,1]]
  let cycle3 := #[#[0,1,0],#[0,0,1],#[1,0,0]]
  let start3 := initialNetwork 2 [true,true,false]
  let some first := networkRound complete3 start3
    | throw (IO.userError "earliest-anchor first round failed")
  let some second := networkRound cycle3 first
    | throw (IO.userError "earliest-anchor second round failed")
  let some third := networkRound complete3 second
    | throw (IO.userError "earliest-anchor third round failed")
  require "audit anchor h=1 with last=2 after a later split"
    (third.all fun state => state.vista.valid && flat state.vista 1 &&
      !flat state.vista 2 &&
      (audit? state.vista 2 3 2).any (fun witness => witness.anchor == 1))
  let some cycleFinal := repeatRounds cycle3 4 start3
    | throw (IO.userError "latest-anchor cycle fixture failed")
  require "audit selects the largest flat anchor h=last=2"
    (cycleFinal.all fun state => state.vista.valid && flat state.vista 2 &&
      (audit? state.vista 2 3 2).any (fun witness => witness.anchor == 2))
  require "singular system rejected"
    ((solveLinear? 2 [(#[1,1],2), (#[2,2],4)]).isNone)
  require "inconsistent overdetermined system rejected"
    ((solveLinear? 1 [(#[1],1), (#[1],2)]).isNone)
  require "rectangular dimensions rejected" ((solveLinear? 2 [(#[1],1)]).isNone)
  require "all overdetermined equations solved"
    (solveLinear? 2 [(#[1,0],2), (#[0,1],3), (#[1,1],5)] == some #[2,3])
  require "fraction rejected as anonymity" ((positiveNaturals? #[(1:ℚ)/2]).isNone)
  require "zero rejected as anonymity" ((positiveNaturals? #[0]).isNone)
  require "negative rejected as anonymity" ((positiveNaturals? #[-1]).isNone)
  require "integral positive anonymous values accepted"
    (positiveNaturals? #[1,3] == some #[1,3])
  let left := updateVista? (initialVista true)
    [(initialVista true, 2), (initialVista false, 3)] 8
  let right := updateVista? (initialVista true)
    [(initialVista false, 3), (initialVista true, 2)] 8
  require "canonical merge independent of input order" (left == right && left.isSome)
  let split := updateVista? (initialVista true)
    [(initialVista true, 1), (initialVista false, 3), (initialVista true, 1)] 8
  require "binary counts aggregate repeated histories" (left == split)
  let huge := updateVista? (initialVista true) [(initialVista true, 2^100)] (2^100)
  require "large multiplicities stay compressed"
    (huge.any fun v => v.nodes.size == 2 &&
      (v.node v.bottom).incoming.length == 1 && v.valid)
  runBoundTest "one agent zero arcs" #[#[0]] 1 [true] 1
  runBoundTest "one agent with large loop bundle" #[#[2^100]] 1 [true] 1
  runBoundTest "two all-leader cycle" #[#[0,1],#[1,0]] 2 [true,true] 2
  runBoundTest "three all-leader cycle" #[#[0,1,0],#[0,0,1],#[1,0,0]]
    3 [true,true,true] 3
  runBoundTest "two agents one leader" #[#[0,1],#[1,1]] 1 [true,false] 3
  runBoundTest "three agents one leader" #[#[0,1,0],#[1,0,1],#[0,1,1]]
    1 [true,false,false] 5
  runBoundTest "three agents two leaders" #[#[0,1,0],#[0,0,1],#[1,0,0]]
    2 [true,true,false] 4
  runBoundTest "parallel arcs" #[#[0,2],#[3,0]] 1 [true,false] 3
  for order in List.range 5 do
    for leaders in List.range (order+1) do
      runVaryingTest (order+1) (leaders+1)
  IO.println "Executable counting tests passed (JSON validation, schedules, malformed/incomplete DAGs, anchor extremes, exact solver, canonical merging, 8 fixed-network and 15 varying-network executions)."

#eval tests

end Counting.Executable.Tests
