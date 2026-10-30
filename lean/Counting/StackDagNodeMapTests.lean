import Counting.StackDagNodeMapBounds
import Counting.StackMachineTestLazy

namespace Counting.StackMachine.DagUpdate.NodeMap.Tests

def tests : IO Unit := do
  let program := referenceMap.program
  let cases : List (List Nat×Executable.Node) :=
    [([],⟨0,none,false,0,[]⟩),([],⟨0,none,true,0,[]⟩),
     ([],⟨1,some 0,false,2,[(0,2)]⟩),
     ([7,9],⟨2,some 1,true,11,[(1,7),(0,4)]⟩),
     ([2,0,2],⟨3,some 2,false,12,[(0,3),(1,4),(2,5)]⟩),
     ([0,0],⟨1,some 7,true,0,[(1,0),(0,5),(1,7)]⟩),
     ([3,1],⟨2^128,some (2^129),false,2^130,[(2^128,7),(0,3)]⟩),
     ([2^129+1,4],⟨7,some 0,true,2^128,[(0,2^128),(1,5)]⟩)]
  let mut maximum := 0
  for (mapping,node) in cases do
    for suffix in [[],[false,true,false,true]] do
      let store : Fin 64→List Bool := fun r=>
        if r=0 then Encoding.node.encode node++suffix
        else if r=1 then (Encoding.list Encoding.natural).encode mapping
        else if 49 ≤ r.val then [true,false]++r.val.bits else []
      let expected := Function.update (Function.update store 0 suffix) 3
        (Encoding.node.encode (Executable.referenceMap mapping.toArray node))
      match TestLazy.finishWithin program 20000000 0 (TestLazy.empty program) ⟨0,store⟩ with
      | none => throw (IO.userError "node referenceMap exceeded test fuel")
      | some (steps,finish) =>
        unless (List.finRange 64).all (fun r=>finish.store r==expected r) do
          throw (IO.userError "node referenceMap full-store mismatch")
        maximum := max maximum steps
  IO.println s!"DAG node referenceMap: 16 full-store tests passed; roots, missing parents, collisions, unsorted edges, zero counts, 131-bit labels and preserved suffix/outside registers; maximum {maximum} instructions."

#eval tests
end Counting.StackMachine.DagUpdate.NodeMap.Tests
