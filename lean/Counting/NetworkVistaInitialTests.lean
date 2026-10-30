import Counting.NetworkVistaInitialSpec
import Counting.StackMachineTestLazy

namespace Counting.StackMachine.NetworkVista.InitialTests
open Routine

def tests : IO Unit := do
  let program:=initialPrefix.program
  let suffix:List Bool:=[true,false,true]
  let tail:List Bool:=[false,true]
  let cases:List (List Bool):=[[],[false],[true],[true,false,true],[false,false,false,false]]
  let mut maximum:=0
  for leaders in cases do
    let store:Store 19:=fun r=>if r=17 then (Encoding.list Encoding.boolean).encode leaders++suffix
      else if r=1 then true::tail else []
    match TestLazy.finishWithin program 100000 0 (TestLazy.empty program) ⟨0,store⟩ with
    | none=>throw (IO.userError "Initial-view construction exhausted fuel")
    | some (time,result)=>
      let expected:=initialPrefixStore store leaders suffix
      unless (List.finRange 21).all (fun r=>result.store r==expected r) do
        throw (IO.userError "Initial-view construction violated its full-store contract")
      unless (Encoding.list Encoding.vista).decodeExact (result.store 20)==
          some (leaders.map Executable.initialVista) do
        throw (IO.userError "Initial-view output failed canonical decoding")
      maximum:=max maximum time
  IO.println s!"Initial views passed {cases.length} full-store cases; maximum {maximum} instructions."

#eval tests
end Counting.StackMachine.NetworkVista.InitialTests
