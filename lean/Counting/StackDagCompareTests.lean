import Counting.StackDagCompare
import Counting.StackMachineTestLazy

namespace Counting.StackMachine.DagUpdate.Key.Tests

def compareTests : IO Unit := do
  let program := compareNodes.program
  let values : List Executable.Node :=
    [⟨0,none,false,0,[]⟩,⟨0,none,true,0,[]⟩,
     ⟨1,some 0,false,3,[(0,2),(1,1)]⟩,
     ⟨1,some 0,false,3,[(0,2),(1,1),(7,0)]⟩,
     ⟨2^128,some (2^129),true,2^130,[(2^127,2^130)]⟩]
  let cases := values.flatMap (fun a=>values.map (a,·))
  let mut maximum := 0
  for value in cases do
    let store : Fin 64→List Bool := fun r=>
      if r=0 then Encoding.node.encode value.1
      else if r=1 then Encoding.node.encode value.2
      else if (2≤r.val && r.val≤13) || (40≤r.val && r.val≤44) || (49≤r.val && r.val≤51) then []
      else [true,false]++r.val.bits
    let expected := nodesComparisonResult store value.1 value.2
    match TestLazy.finishWithin program 2000000 0 (TestLazy.empty program) ⟨0,store⟩ with
    | none => throw (IO.userError "DAG key comparator exceeded fuel")
    | some (steps,finish) =>
      unless (List.finRange 64).all (fun r=>finish.store r==expected r) do
        throw (IO.userError "DAG key comparator full-store mismatch")
      maximum := max maximum steps
  IO.println s!"DAG node comparator: {cases.length} full-store cases passed; maximum {maximum} instructions."

#eval compareTests
end Counting.StackMachine.DagUpdate.Key.Tests
