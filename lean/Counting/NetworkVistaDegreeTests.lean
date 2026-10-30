import Counting.NetworkVistaDegree
import Counting.StackMachineTestLazy

namespace Counting.StackMachine.NetworkVista.DegreeTests
open Routine

def tests : IO Unit := do
  let program:=rowTotal.program
  let rows:List (Array Nat):=[#[],#[0],#[0,0,0],#[1,2,3],#[2^129,0,2^129+1]]
  let mut maximum:=0
  for row in rows do
    let store:Store 20:=fun r=>if r=21 then (Encoding.array Encoding.natural).encode row else []
    match TestLazy.finishWithin program 500000 0 (TestLazy.empty program) ⟨0,store⟩ with
    | none=>throw (IO.userError "Binary outdegree summation exhausted fuel")
    | some (time,result)=>
      let expected:=Function.update store 19 row.toList.sum.bits
      unless (List.finRange 22).all (fun r=>result.store r==expected r) do
        throw (IO.userError "Binary outdegree summation violated its full-store contract")
      maximum:=max maximum time
  IO.println s!"Binary outdegree passed {rows.length} full-store cases; maximum {maximum} instructions."

#eval tests
end Counting.StackMachine.NetworkVista.DegreeTests
