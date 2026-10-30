import Counting.NetworkVistaBundleFinish
import Counting.StackMachineTestLazy

namespace Counting.StackMachine.NetworkVista.BundleFinishTests
open Routine

def tests : IO Unit := do
  let cases:List (List (Executable.Vista×Nat)) := [[],[(Executable.initialVista true,1)],
    [(Executable.initialVista false,2),(Executable.initialVista true,3)],
    [(Executable.initialVista true,2^129+1)]]
  let program:=finishBundles.program
  let mut maximum:=0
  for messages in cases do
    let codec:=Encoding.product Encoding.vista Encoding.natural
    let store:Store 38:=fun r=>if r=24 then (Encoding.sequence codec messages).reverse
      else if r=25 then List.replicate messages.length true
      else if 27≤r.val && r.val≤30 then [] else [true,false]
    let expected:=Function.update (Function.update (Function.update store 24 []) 25 [])
      27 ((Encoding.list codec).encode messages)
    match TestLazy.finishWithin program 100000 0 (TestLazy.empty program) ⟨0,store⟩ with
    | none=>throw (IO.userError "Bundle list framing exhausted fuel")
    | some (time,result)=>
      unless (List.finRange 40).all (fun r=>result.store r==expected r) do
        throw (IO.userError "Bundle list framing violated its full-store contract")
      maximum:=max maximum time
  IO.println s!"Bundle list framing passed {cases.length} full-store cases; maximum {maximum} instructions."

#eval tests
end Counting.StackMachine.NetworkVista.BundleFinishTests
