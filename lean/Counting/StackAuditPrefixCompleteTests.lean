import Counting.StackAuditPrefixComplete
import Counting.StackMachineTestLazy

namespace Counting.StackMachine.AuditPrefix.CompleteTests
open Routine

def tests : IO Unit := do
  let p:=complete.program
  let root:=Executable.initialVista true
  let next : Executable.Vista:=⟨#[⟨0,none,true,0,[]⟩,⟨1,some 0,true,0,[]⟩],1⟩
  let chain : Executable.Vista:=⟨#[⟨0,none,true,0,[]⟩,⟨1,some 0,true,0,[]⟩,
    ⟨2,some 1,true,0,[]⟩,⟨3,some 2,true,0,[]⟩],3⟩
  let plain : Executable.Vista:=⟨#[⟨0,none,false,0,[]⟩,⟨1,some 0,false,0,[]⟩],1⟩
  let some incomplete:=Executable.updateVista? root [(Executable.initialVista false,1)] 1
    | throw (IO.userError "Prefix incomplete-child fixture failed")
  let cases : List (String×Executable.Vista×Nat×Nat×Nat×Option Nat):=
    [("empty malformed vista",⟨#[],0⟩,1,1,1,none),
     ("insufficient depth",root,1,1,1,none),
     ("zero last round",root,1,1,0,none),
     ("first anchor",next,1,1,1,some 1),
     ("latest of two anchors",chain,1,1,2,some 2),
     ("latest of three anchors",chain,1,1,3,some 3),
     ("zero leaders",next,0,1,1,none),
     ("candidate below leaders",next,2,1,1,none),
     ("binary oversized last",next,1,1,2^80+1,none),
     ("no visible leader",plain,1,1,1,none),
     ("missing child",incomplete,1,2,1,none)]
  for (name,vista,leaders,candidate,last,answer) in cases do
    unless Executable.auditPrefix? vista leaders candidate last==answer do
      throw (IO.userError s!"Prefix fixture has unexpected specification: {name}")
    let input:=inputWord vista leaders candidate last
    let output:=Encoding.optionalNatural.encode answer
    let before:=inputStore 50 input
    let after:=outputStore 50 output
    match TestLazy.finishWithin p 20000000 0 (TestLazy.empty p) ⟨0,before⟩ with
    | none=>throw (IO.userError s!"Complete prefix regression exhausted fuel: {name}")
    | some (steps,finish)=>
      unless (List.finRange 52).all (fun r=>finish.store r==after r) do
        throw (IO.userError s!"Complete prefix result or register cleanup mismatch: {name}")
      unless steps≤completeCoefficient*(input.length+1)^7 do
        throw (IO.userError s!"Complete prefix exceeded its proved bound: {name}")
      IO.println s!"Complete prefix {name}: {steps} instructions, answer {repr answer}; all 52 registers checked."
  IO.println "Eleven complete prefix regressions passed."

#eval tests
end Counting.StackMachine.AuditPrefix.CompleteTests
