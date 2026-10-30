import Counting.ExecutableRefinementCore
import Counting.Simulation

/-! Runtime checks for the separately exposed core program. These execute
the real binary-bundle updater and exact audit; the general proofs are in
ExecutableRefinementCoreCorrectness and ExecutableRefinementCorePhysical. -/
namespace Counting.Executable.CoreTests
open Counting.Simulation

private def require (name : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError s!"Core executable test failed: {name}")

def coreNetworkRound (graph : RoundGraph) (states : Array LocalState) : Option (Array LocalState) := do
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
    let next ← advanceCore? state received outgoing.toList.sum
    result := result.push next
  return result

def checkCore (name : String) (graph : RoundGraph) (ell : Nat) (labels : List Bool) : IO Unit := do
  let mut states := initialNetwork ell labels
  for round in List.range (2 * labels.length - 1) do
    require s!"{name}: no early output at {round}" (states.all (fun state => state.output.isNone))
    let some next := coreNetworkRound graph states
      | throw (IO.userError s!"{name}: transition rejected")
    require s!"{name}: valid DAG at {round+1}" (next.all (fun state => state.vista.valid))
    states := next
  require s!"{name}: simultaneous exact output" (states.all (fun state => state.output == some labels.length))
  let some frozen := coreNetworkRound graph states
    | throw (IO.userError s!"{name}: halted transition rejected")
  require s!"{name}: halted state unchanged" (frozen == states)

def tests : IO Unit := do
  checkCore "singleton without loops" #[#[0]] 1 [true]
  checkCore "singleton binary loop" #[#[2^100]] 1 [true]
  checkCore "all leaders core takes 2n−1" #[#[0,1],#[1,0]] 2 [true,true]
  checkCore "one leader" #[#[0,1,0],#[1,0,1],#[0,1,1]] 1 [true,false,false]
  checkCore "several leaders core takes 2n−1" #[#[0,1,0],#[0,0,1],#[1,0,0]] 2 [true,true,false]
  require "zero leaders rejected" ((advanceCore? (initialState 0 true) [] 0).isNone)
  require "zero message multiplicity rejected"
    ((advanceCore? (initialState 1 true) [(initialVista false,0)] 0).isNone)
  IO.println "Core executable tests passed (5 physical executions, invalid leader/message inputs)."

#eval tests
end Counting.Executable.CoreTests
