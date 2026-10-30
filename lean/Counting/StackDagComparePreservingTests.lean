import Counting.StackDagComparePreserving
import Counting.StackMachineTestLazy

namespace Counting.StackMachine.DagUpdate.Key.Tests

def preservingTests : IO Unit := do
  let program := preservingNodes.program
  let cases : List (Executable.Node×Executable.Node) :=
    [(⟨0,none,false,0,[]⟩,⟨0,none,true,0,[]⟩),
     (⟨1,some 0,false,3,[(0,2)]⟩,⟨1,some 0,false,3,[(0,2)]⟩),
     (⟨1,some 0,false,3,[(0,2),(1,0)]⟩,⟨1,some 0,false,3,[(0,2)]⟩),
     (⟨2^128,some (2^129),true,2^130,[(2^127,2^130)]⟩,⟨0,none,false,0,[]⟩)]
  let mut maximum := 0
  for value in cases do
    let store : Fin 72→List Bool := fun r=>
      if r=64 then Encoding.node.encode value.1
      else if r=65 then Encoding.node.encode value.2
      else if r.val≤13 || (40≤r.val && r.val≤44) || (49≤r.val && r.val≤51) || r=67 then []
      else [false,true]++r.val.bits
    let expected := Function.update store 66 (Executable.lexLE value.1.key value.2.key::store 66)
    match TestLazy.finishWithin program 2000000 0 (TestLazy.empty program) ⟨0,store⟩ with
    | none => throw (IO.userError "Preserving DAG comparator exceeded fuel")
    | some (steps,finish) =>
      unless (List.finRange 72).all (fun r=>finish.store r==expected r) do
        throw (IO.userError "Preserving DAG comparator full-store mismatch")
      maximum := max maximum steps
  IO.println s!"Preserving DAG node comparator: {cases.length} full-store cases passed; maximum {maximum} instructions."

#eval preservingTests
end Counting.StackMachine.DagUpdate.Key.Tests
