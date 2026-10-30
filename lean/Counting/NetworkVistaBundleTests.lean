import Counting.NetworkVistaBundle
import Counting.StackMachineTestLazy

namespace Counting.StackMachine.NetworkVista.BundleTests
open Routine

def tests : IO Unit := do
  let program:=appendReceivedBundle.program
  let rows:List (Array Nat):=[#[0],#[1],#[0,2,0],#[2^129,0,2^129+1]]
  let view:=Executable.initialVista true
  let mut count:=0
  let mut maximum:=0
  for row in rows do
    for index in List.range row.size do
      let store:Store 14:=fun r=>if r=0 then Encoding.vista.encode view
        else if r=1 then (Encoding.array Encoding.natural).encode row
        else if r=2 then List.replicate index true
        else if r=3 then [false,true,false]
        else if r=4 then [true,true]
        else if r=13 || r=14 || r=15 then [false,true] else []
      let expected:=receivedBundleStore store view (row[index]?.getD 0)
      match TestLazy.finishWithin program 200000 0 (TestLazy.empty program) ⟨0,store⟩ with
      | none=>throw (IO.userError "Received-bundle construction exhausted fuel")
      | some (time,result)=>
        unless (List.finRange 16).all (fun r=>result.store r==expected r) do
          throw (IO.userError "Received-bundle construction violated full-store preservation or binary filtering")
        maximum:=max maximum time
        count:=count+1
  IO.println s!"Received binary bundles passed {count} full-store cases; maximum {maximum} instructions."

#eval tests
end Counting.StackMachine.NetworkVista.BundleTests
