import Counting.NetworkVistaSenderLoop
import Counting.StackMachineTestLazy

namespace Counting.StackMachine.NetworkVista.SenderTests
open Routine

def tests : IO Unit := do
  let program:=(forEach 26 senderItem).program
  let cases:List (Nat×List (Executable.Vista×Array Nat)) := [
    (0,[]),
    (0,[(Executable.initialVista true,#[0])]),
    (0,[(Executable.initialVista false,#[2])]),
    (1,[(Executable.initialVista true,#[0,0]),(Executable.initialVista false,#[1,3]),
      (Executable.initialVista false,#[1,0])]),
    (0,[(Executable.initialVista true,#[2^129]),(Executable.initialVista false,#[0]),
      (Executable.initialVista true,#[2^129+1])])]
  let viewSuffix:List Bool:=[true,false]
  let rowSuffix:List Bool:=[false,true,true]
  let mut maximum:=0
  for (receiver,pairs) in cases do
    let store:Store 38:=fun r=>if r=1 then [false,true]
      else if r=21 then Encoding.sequence Encoding.vista (pairs.map Prod.fst)++viewSuffix
      else if r=22 then Encoding.sequence (Encoding.array Encoding.natural) (pairs.map Prod.snd)++rowSuffix
      else if r=23 then List.replicate receiver true
      else if r=24 then [false,true,false] else if r=25 then [true,true]
      else if r=26 then List.replicate pairs.length true
      else if (17≤r.val && r.val≤20) || 37≤r.val then [false,true] else []
    let expected:=senderLoopStore store receiver pairs viewSuffix rowSuffix
    match TestLazy.finishWithin program 3000000 0 (TestLazy.empty program) ⟨0,store⟩ with
    | none=>throw (IO.userError "Sender stream loop exhausted fuel")
    | some (time,result)=>
      unless (List.finRange 40).all (fun r=>result.store r==expected r) do
        throw (IO.userError "Sender stream loop violated complete store or sender order")
      maximum:=max maximum time
  IO.println s!"Sender streams passed {cases.length} full-store cases; maximum {maximum} instructions."

#eval tests
end Counting.StackMachine.NetworkVista.SenderTests
