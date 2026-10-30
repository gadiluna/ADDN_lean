import Counting.StackAuditBalancePrepareRounds
import Counting.StackMachineTestLazy

namespace Counting.StackMachine.AuditBalance.PrepareTests
open Routine

def tests : IO Unit := do
  let p:=prepareBalanceRounds.program
  for (anchor,n) in ([(0,0),(1,1),(4,4),(5,3),(2^80+17,3)] : List (Nat×Nat)) do
    let before : Store 48:=fun i=>if i=36 then anchor.bits else if i=49 then List.replicate n true
      else if i=34 then [false,true,false] else if i=1 then [false] else if i=45 then [true,true] else []
    let after:=Function.update (Function.update (Function.update before 36 []) 48
      (List.replicate (min anchor n-1) true)) 22 [true]
    match TestLazy.finishWithin p 3000000 0 (TestLazy.empty p) ⟨0,before⟩ with
    | none=>throw (IO.userError "Balance bounded-anchor preparation exhausted regression fuel")
    | some (steps,last)=>
      unless (List.finRange (p.extraRegisters+2)).all (fun r=>last.store r==after r) do
        throw (IO.userError "Balance bounded-anchor counter, sentinel or cleanup mismatch")
      unless steps≤1200*(n+anchor.size+1)^3 do
        throw (IO.userError "Balance preparation exceeded its proved bound")
      IO.println s!"Balance preparation anchor {anchor}, node budget {n}: {steps} transitions."
  IO.println "Five balance preparation regressions passed, including an 81-bit anchor."

#eval tests
end Counting.StackMachine.AuditBalance.PrepareTests
