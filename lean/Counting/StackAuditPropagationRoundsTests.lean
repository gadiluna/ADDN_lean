import Counting.StackAuditPropagationRounds
import Counting.StackMachineTestLazy

namespace Counting.StackMachine.AuditPropagation.RoundTests

def tests : IO Unit := do
  let p:=preparePropagationRounds.program
  let cases : List (Nat×Nat):=[(0,0),(0,3),(2,3),(7,3),(2^80,2)]
  for (anchor,n) in cases do
    let before : Register p→List Bool:=fun r=>
      if r.val=42 then anchor.bits else if r.val=40 then List.replicate n true
      else if r.val=1 then [true] else if r.val=35 then [false,true,false]
      else if r.val=34 then [true,false,true] else []
    match TestLazy.finishWithin p 2000000 0 (TestLazy.empty p) ⟨0,before⟩ with
    | none=>throw (IO.userError "Propagation bounded-round counter exhausted fuel")
    | some (steps,last)=>
      unless (List.finRange (p.extraRegisters+2)).all
        (fun r=>last.store r==(if r.val=41 then List.replicate (min anchor n) true else before r)) do
        throw (IO.userError "Propagation bounded-round counter/full store mismatch")
      IO.println s!"Propagation bounded rounds: {anchor.size} anchor bits, {n} nodes, {steps} transitions."
  IO.println "Five bounded-round counter regressions passed; all 44 registers checked."

#eval tests
end Counting.StackMachine.AuditPropagation.RoundTests
