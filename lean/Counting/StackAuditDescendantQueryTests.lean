import Counting.StackAuditDescendantQuery
import Counting.StackMachineTestLazy

namespace Counting.StackMachine.AuditDescendant.QueryTests
open Routine

def tests : IO Unit := do
  let cases:List (List Bool):=[[],[false],[true],[false,true,false],List.replicate 17 false,List.replicate 130 true]
  let program:=prepareQuery.program
  let mut maximum:=0
  for bits in cases do
    let store : Store 46:=fun r=>
      if r=43 then bits else if r=0 ∨ r=18 ∨ r=31 ∨ r=33 then [] else [true,false,false]
    let expected:=Function.update store 33 (Encoding.natural.encode bits.length)
    match TestLazy.finishWithin program 2000000 0 (TestLazy.empty program) ⟨0,store⟩ with
    | none=>throw (IO.userError "Descendant index query exceeded regression fuel")
    | some (time,finish)=>
      unless (List.finRange 48).all (fun r=>finish.store r==expected r) do
        throw (IO.userError "Descendant index query full-store mismatch")
      maximum:=max maximum time
  IO.println s!"Descendant canonical weight query: {cases.length} full-store tests passed; empty and mixed-bit counters, framing and preserved external registers; maximum {maximum} instructions."

#eval tests
end Counting.StackMachine.AuditDescendant.QueryTests
