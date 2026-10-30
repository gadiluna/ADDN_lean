import Counting.StackAuditDescendantRounds
import Counting.StackMachineTestLazy

namespace Counting.StackMachine.AuditDescendant.RoundsTests
open Routine

def tests : IO Unit := do
  let cases : List (Nat×Nat×Nat):=
    [(0,0,0),(0,3,4),(3,0,4),(3,1,4),(3,3,4),(3,4,4),(5,2,3),
      (2^130,0,3),(2^130,2^129,3),(3,2^130,3),(2^130,0,0)]
  let program:=prepareRounds.program
  let mut maximum:=0
  for (last,anchor,n) in cases do
    let store : Store 46:=fun r=>
      if r=34 then last.bits else if r=40 then anchor.bits
      else if r=44 then List.replicate n true
      else if r∈roundWorkspace then [] else [false,true,false]
    let expected:=Function.update store 38 (List.replicate (min last n-min anchor n) true)
    match TestLazy.finishWithin program 2000000 0 (TestLazy.empty program) ⟨0,store⟩ with
    | none=>throw (IO.userError "Bounded descendant round preparation exceeded regression fuel")
    | some (time,finish)=>
      unless (List.finRange 48).all (fun r=>finish.store r==expected r) do
        throw (IO.userError "Bounded descendant round preparation full-store mismatch")
      maximum:=max maximum time
  IO.println s!"Bounded descendant rounds: {cases.length} full-store tests passed; zero budgets, truncated subtraction, 131-bit labels, clipped counts and external sentinels; maximum {maximum} instructions."

#eval tests
end Counting.StackMachine.AuditDescendant.RoundsTests
