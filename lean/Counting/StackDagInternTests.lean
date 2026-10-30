import Counting.StackDagIntern
import Counting.StackMachineTestLazy

namespace Counting.StackMachine.DagUpdate.Intern.Tests

def tests : IO Unit := do
  let program := internNode.program
  let root : Executable.Node := ⟨0,none,false,0,[]⟩
  let leader : Executable.Node := ⟨0,none,true,0,[]⟩
  let child : Executable.Node := ⟨1,some 0,false,3,[(0,2),(1,1)]⟩
  let changed : Executable.Node := ⟨1,some 1,false,3,[(0,2),(1,1)]⟩
  let huge : Executable.Node := ⟨2^128,some (2^129),true,2^130,[(2^127,2^130)]⟩
  let cases : List (List Executable.Node×Executable.Node) :=
    [([],root),([],huge),([root],root),([root],leader),([root,leader],leader),
     ([root,leader,root],root),([child,child,root],child),([child],changed),
     ([root,child],child),([root,leader],child),([huge,root,huge],huge),([root,child],huge)]
  let mut maximum := 0
  for (nodes,query) in cases do
    let store : Fin 64→List Bool := fun r=>
      if r=0 then (Encoding.list Encoding.node).encode nodes
      else if r=1 then Encoding.node.encode query
      else if 38 ≤ r.val then [true,false]++r.val.bits else []
    let result := Executable.intern nodes.toArray query
    let expected := Function.update (Function.update store 2 ((Encoding.array Encoding.node).encode result.1))
      3 result.2.bits
    match TestLazy.finishWithin program 20000000 0 (TestLazy.empty program) ⟨0,store⟩ with
    | none => throw (IO.userError "DAG intern exceeded test fuel")
    | some (steps,finish) =>
      unless (List.finRange 64).all (fun r=>finish.store r==expected r) do
        throw (IO.userError "DAG intern full-store mismatch")
      maximum := max maximum steps
  IO.println s!"DAG intern: {cases.length} full-store tests passed; empty tables, first duplicates, differing signatures, 131-bit labels, input preservation and external sentinels; maximum {maximum} instructions."

#eval tests
end Counting.StackMachine.DagUpdate.Intern.Tests
