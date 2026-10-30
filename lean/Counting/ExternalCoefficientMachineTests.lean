import Counting.ExternalCoefficientMachine
import Counting.StackMachineTestLazy

namespace Counting.External.CoefficientMachine.MachineTests
open StackMachine
def tests : IO Unit := do
  let program:=stackGenerator
  let raws : List X3CEncoding.Raw :=
    [([],[]),(List.replicate 3 true,[]),(List.replicate 3 true,[[0,1,2]]),
      (List.replicate 6 true,[[0,1,2],[3,4,5]]),(List.replicate 3 true,[[0,1,2],[0,1,2]]),
      ([false,true,true],[[0,1,2]]),(List.replicate 4 true,[[0,1,2]]),
      (List.replicate 3 true,[[0,0,2]]),(List.replicate 3 true,[[2,0,1]]),
      (List.replicate 3 true,[[0,1,3]]),(List.replicate 3 true,[[0,1,2^128]]),
      (List.replicate 3 true,[[0,1]])]
  let words:=[[],[true]]++raws.map X3CEncoding.rawCodec.encode
  let mut maximum:=0
  for word in words do
    match TestLazy.finishWithin program 10000000 0 (TestLazy.empty program) (initial program word) with
    | none=>throw (IO.userError "total coefficient transducer exceeded test fuel")
    | some (steps,finish)=>
      unless finish.store 1==computeCoefficients word do
        throw (IO.userError "total coefficient transducer output mismatch")
      maximum:=max maximum steps
  IO.println s!"X3C coefficient total transducer: {words.length} stack output cases passed; malformed, empty, duplicate, out-of-order and 129-bit indices; maximum {maximum} instructions."
#eval tests
end Counting.External.CoefficientMachine.MachineTests
