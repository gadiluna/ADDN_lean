import Counting.StackAuditPrefixOpening
import Counting.StackMachineTestLazy

namespace Counting.StackMachine.AuditPrefix.OpeningTests
open Routine

def tests : IO Unit := do
  let p:=opening.program
  let root:=Executable.initialVista true
  let next:Executable.Vista:=⟨#[⟨0,none,true,0,[]⟩,⟨1,some 0,true,0,[]⟩],1⟩
  let cases:List (Executable.Vista×Nat×Nat×Nat):=
    [(⟨#[],0⟩,1,1,1),(root,1,1,1),(next,1,1,1),(next,2,1,1),(next,1,1,2^80+1)]
  for (vista,leaders,candidate,last) in cases do
    let input:=inputWord vista leaders candidate last
    let before:=inputStore 50 input
    let accepted:=openingAccepted vista leaders candidate last
    let expected:=openingFile vista leaders candidate last accepted
    match TestLazy.finishWithin p 10000000 0 (TestLazy.empty p) ⟨0,before⟩ with
    | none=>throw (IO.userError "Audit prefix opening exhausted regression fuel")
    | some (steps,finish)=>
      unless (List.finRange 52).all (fun r=>finish.store r==expected r) do
        throw (IO.userError "Audit prefix opening status/table/metadata/scratch mismatch")
      unless steps≤230000000*(input.length+1)^6 do
        throw (IO.userError "Audit prefix opening exceeded its proved polynomial bound")
      IO.println s!"Opening {vista.nodes.size} nodes, last {last}: {steps} transitions, result {accepted}."
  IO.println "Five prefix opening regressions passed; all 52 registers checked."

#eval tests
end Counting.StackMachine.AuditPrefix.OpeningTests
