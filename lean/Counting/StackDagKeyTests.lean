import Counting.StackDagKeyBounds
import Counting.StackMachineTestLazy

namespace Counting.StackMachine.DagUpdate.Key.Tests

def tests : IO Unit := do
  let program := encodeKey.program
  let cases : List Executable.Node :=
    [⟨0,none,false,0,[]⟩,⟨0,none,true,0,[]⟩,
     ⟨1,some 0,false,3,[(0,2),(1,1)]⟩,
     ⟨3,some 2,true,0,[(5,0),(1,7),(5,3)]⟩,
     ⟨2^128,some (2^129),true,2^130,[(2^127,2^130)]⟩,
     ⟨7,none,false,9,[(8,6),(3,2)]⟩]
  let mut maximum := 0
  for node in cases do
    let store : Fin 64→List Bool := fun r=>
      if r=0 then Encoding.node.encode node
      else if r=3 || (40 ≤ r.val && r.val ≤ 44) || r=49 then []
      else [false,true]++r.val.bits
    let expected := Function.update (Function.update store 0 []) 3 (Encoding.sequence Encoding.natural node.key)
    match TestLazy.finishWithin program 100000 0 (TestLazy.empty program) ⟨0,store⟩ with
    | none => throw (IO.userError "DAG key encoding exceeded fuel")
    | some (steps,finish) =>
      unless (List.finRange 64).all (fun r=>finish.store r==expected r) do
        throw (IO.userError "DAG key encoding full-store mismatch")
      unless steps==keyBudget node do
        throw (IO.userError "DAG key encoding exact cost mismatch")
      maximum := max maximum steps
  IO.println s!"DAG numeric key: {cases.length} full-store cases passed with exact cost; maximum {maximum} instructions."

#eval tests
end Counting.StackMachine.DagUpdate.Key.Tests
