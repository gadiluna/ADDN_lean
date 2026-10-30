import Counting.NetworkVistaCollectActual
import Counting.StackMachineTestLazy

namespace Counting.StackMachine.NetworkVista.CollectPreservingTests
open Routine

def tests : IO Unit := do
  let program:=collectPreserving.program
  let cases:List (Nat×List (Executable.Vista×Array Nat)) := [
    (0,[]),
    (0,[(Executable.initialVista true,#[0])]),
    (0,[(Executable.initialVista false,#[2])]),
    (1,[(Executable.initialVista true,#[0,0,1]),(Executable.initialVista false,#[1,3,0]),
      (Executable.initialVista false,#[1,0,0])]),
    (0,[(Executable.initialVista true,#[2^129,0,1]),(Executable.initialVista false,#[0,1,0]),
      (Executable.initialVista true,#[2^129+1,0,0])])]
  let mut maximum:=0
  for (receiver,pairs) in cases do
    let store:Store 38:=fun r=>if r=1 then [false,true]
      else if r=37 then (Encoding.list Encoding.vista).encode (pairs.map Prod.fst)
      else if r=38 then (Encoding.list (Encoding.array Encoding.natural)).encode (pairs.map Prod.snd)
      else if r=23 then List.replicate receiver true
      else if (17≤r.val && r.val≤20) || r=39 then [false,true] else []
    let expected:=Function.update store 27
      ((Encoding.list (Encoding.product Encoding.vista Encoding.natural)).encode (receivedPairs receiver pairs))
    match TestLazy.finishWithin program 5000000 0 (TestLazy.empty program) ⟨0,store⟩ with
    | none=>throw (IO.userError "Preserving compact message collection exhausted fuel")
    | some (time,result)=>
      unless (List.finRange 40).all (fun r=>result.store r==expected r) do
        throw (IO.userError "Preserving compact collector changed source arrays or scratch registers")
      maximum:=max maximum time
  IO.println s!"Preserving compact collection passed {cases.length} full-store cases; maximum {maximum} instructions."

#eval tests
end Counting.StackMachine.NetworkVista.CollectPreservingTests
