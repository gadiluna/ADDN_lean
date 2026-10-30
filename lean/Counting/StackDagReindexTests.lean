import Counting.StackDagReindexBounds
import Counting.StackMachineTestLazy

namespace Counting.StackMachine.DagUpdate.Reindex.Tests

def tests : IO Unit := do
  let program:=incoming.program
  let cases : List (List Nat×List (Nat×Nat)) :=
    [([],[]),([],[(0,3),(7,4)]),([2,0,2],[(0,3),(1,4),(2,5)]),
     ([0,0],[(1,0),(0,5),(1,7)]),([3,1],[(2^128,7),(0,3)]),
     ([2^129+1,4],[(0,2^128),(1,5)]),([1,2,3],[(2,7),(0,9),(1,11)]),
     ([2,1],[(0,0),(1,0)])]
  let mut maximum:=0
  for (mapping,source) in cases do
    for initial in [[],[(2,1),(0,2)]] do
      let suffix:=[false,true,false,true]
      let store : Fin 40→List Bool:=fun r=>
        if r=0 then (Encoding.list edgeCodec).encode source++suffix
        else if r=1 then (Encoding.list Encoding.natural).encode mapping
        else if r=2 then (Encoding.list edgeCodec).encode initial
        else if r=38 then [true,false,true] else if r=39 then [false,false,true,true] else []
      let expected:=Function.update (Function.update store 0 suffix) 2
        ((Encoding.list edgeCodec).encode (source.foldl (remap mapping) initial))
      match TestLazy.finishWithin program 10000000 0 (TestLazy.empty program) ⟨0,store⟩ with
      | none=>throw (IO.userError "incoming reference fold exceeded test fuel")
      | some (steps,finish)=>
        unless (List.finRange 40).all (fun r=>finish.store r==expected r) do
          throw (IO.userError "incoming reference fold full-store mismatch")
        maximum:=max maximum steps
  IO.println s!"DAG referenceMap incoming: 16 full-store tests passed; empty/out-of-range/zero/colliding/reordered references, 130-bit indices/counts, arbitrary initial accumulator and sentinels; maximum {maximum} instructions."

#eval tests
end Counting.StackMachine.DagUpdate.Reindex.Tests
