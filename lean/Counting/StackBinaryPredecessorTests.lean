import Counting.StackBinaryPredecessor
import Counting.StackMachineTestLazy

namespace Counting.StackMachine.Binary.Tests

private def workspace : PredWorkspace 2 := ⟨![7,0,8,1,5,3,2,6],by decide⟩

def predecessorTests : IO Unit := do
  let program := (predecessor 2 workspace).program
  let cases := List.range 17++[31,32,33,255,256,257,2^128-1,2^128,2^128+1,2^1024]
  let mut maximum := 0
  for n in cases do
    let store : Fin 10→List Bool := fun r=>
      if r=workspace 0 then n.bits
      else if r=4 then [true,false,true]
      else if r=9 then [false,true,true] else []
    let expected := Function.update store (workspace 1) (n-1).bits
    match TestLazy.finishWithin program 1000000 0 (TestLazy.empty program) ⟨0,store⟩ with
    | none=>throw (IO.userError "binary predecessor exhausted test fuel")
    | some (steps,finish)=>
      unless (List.finRange 10).all (fun r=>finish.store r==expected r) do
        throw (IO.userError "binary predecessor full-store mismatch")
      unless steps ≤ 60*(n.size+1) do
        throw (IO.userError "binary predecessor exceeded proved bit bound")
      maximum := max maximum steps
  IO.println s!"Binary predecessor: {cases.length} full-store cases passed; maximum {maximum} stack transitions."

#eval predecessorTests
end Counting.StackMachine.Binary.Tests
