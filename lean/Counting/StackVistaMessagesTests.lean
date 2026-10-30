import Counting.StackVistaMessagesPolynomial
import Counting.StackMachineTestLazy

namespace Counting.StackMachine.DagUpdate.Receive.Tests
open Routine

def tests : IO Unit := do
  let program := completeMessages.program
  let leader := Executable.initialVista true
  let follower := Executable.initialVista false
  let cases : List (String×Executable.MergeState×List (Executable.Vista×Nat)) :=
    [("empty messages",(#[],[]),[]),
     ("one leader message",(#[],[]),[(leader,1)]),
     ("repeated signature",(leader.nodes,[]),[(leader,1),(leader,2)]),
     ("two initial labels",(leader.nodes,[]),[(follower,1),(leader,3)]),
     ("zero multiplicity",(#[],[]),[(leader,0)]),
     ("binary multiplicity",(#[],[]),[(leader,2^40+7)]),
     ("malformed empty DAG",(#[],[]),[(⟨#[],5⟩,2)]),
     ("existing incoming counts",(leader.nodes,[(0,4)]),[(leader,3)])]
  for (name,state,messages) in cases do
    let input := messagesInput state messages
    let answer := outputStore 94 (messagesOutput state messages)
    match TestLazy.finishWithin program 20000000 0 (TestLazy.empty program)
        ⟨0,inputStore 94 input⟩ with
    | none => throw (IO.userError s!"Message fold exhausted fuel: {name}")
    | some (steps,last) =>
      unless (List.finRange 96).all (fun r=>last.store r==answer r) do
        throw (IO.userError s!"Message fold output or cleanup mismatch: {name}")
      unless steps≤completeMessagesCoefficient*(input.length+1)^61 do
        throw (IO.userError s!"Message fold exceeded proved bound: {name}")
      IO.println s!"Message fold {name}: {steps} instructions; all 96 registers checked."
  IO.println "Eight message fold regressions passed."

#eval tests
end Counting.StackMachine.DagUpdate.Receive.Tests
