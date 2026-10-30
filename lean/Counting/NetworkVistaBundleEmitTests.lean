import Counting.NetworkVistaBundleEmit
import Counting.StackMachineTestLazy

namespace Counting.StackMachine.NetworkVista.BundleEmitTests
open Routine

def tests : IO Unit := do
  let program:=emitBundle.program
  let mut count:=0
  for view in [Executable.initialVista false,Executable.initialVista true] do
    for amount in [0,1,2,2^129+1] do
      let store:Store 14:=fun r=>if r=0 then Encoding.vista.encode view
        else if r=3 then [false,true,false] else if r=4 then [true,true]
        else if r=5 then amount.bits else if r=8 || r=9 then [] else [false,true]
      match TestLazy.finishWithin program 100000 0 (TestLazy.empty program) ⟨0,store⟩ with
      | none=>throw (IO.userError "Binary bundle emitter exhausted fuel")
      | some (time,result)=>
        unless (List.finRange 16).all (fun r=>result.store r==emitBundleStore store r) do
          throw (IO.userError "Binary bundle emitter violated its full-store contract")
        unless time==7*(store 0).length+9*amount.size+15 do
          throw (IO.userError "Binary bundle emitter violated its exact cost")
        count:=count+1
  IO.println s!"Binary bundle emitter passed {count} full-store and exact-cost cases."

#eval tests
end Counting.StackMachine.NetworkVista.BundleEmitTests
