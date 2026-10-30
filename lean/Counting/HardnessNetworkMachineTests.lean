import Counting.HardnessNetworkMachineEntry
import Counting.StackMachineTestLazy

namespace Counting.HardnessNetworkMachine.Tests
open StackMachine

def tests : IO Unit := do
  let program:=networkEntry.program
  let raws : List X3CEncoding.Raw :=
    [([],[]),(List.replicate 3 true,[]),(List.replicate 3 true,[[0,1,2]]),
      (List.replicate 6 true,[[0,1,2],[3,4,5]]),
      ([false,true,true],[[0,1,2]]),(List.replicate 4 true,[[0,1,2]]),
      (List.replicate 3 true,[[0,0,2]]),(List.replicate 3 true,[[2,0,1]]),
      (List.replicate 3 true,[[0,1,2^128]]),(List.replicate 3 true,[[0,1]])]
  let words:=[[],[true]]++raws.map X3CEncoding.rawCodec.encode
  let mut maximum:=0
  for word in words do
    match TestLazy.finishWithin program 50000000 0 (TestLazy.empty program) (initial program word) with
    | none=>throw (IO.userError "total hardness network generator exceeded fuel")
    | some (steps,finish)=>
      unless finish.store 1==networkTransform word do
        throw (IO.userError "total hardness network generator output mismatch")
      maximum:=max maximum steps
  IO.println s!"Hardness network transducer: {words.length} total stack output cases passed; empty, positive/negative, malformed and 129-bit indices; maximum {maximum} instructions."

#eval tests
end Counting.HardnessNetworkMachine.Tests
