import Counting.StackDagAddCountBounds
import Counting.StackMachineTestLazy

namespace Counting.StackMachine.DagUpdate.Tests

def roles : AddWorkspace 1 := ⟨fun i=>⟨i.val+1,by omega⟩,by
  intro a b h
  apply Fin.ext
  have eq:=congrArg (fun i : Fin 21=>i.val) h
  dsimp at eq
  omega⟩

def tests : IO Unit := do
  let program:=(addCount 1 roles).program
  let cases : List (Nat×Nat×List (Nat×Nat)) :=
    [(0,0,[]),(0,1,[]),(7,0,[(1,3),(7,4)]),(0,2,[(1,3),(7,4)]),
     (1,2,[(1,3),(7,4)]),(4,2,[(1,3),(7,4)]),(7,2,[(1,3),(7,4)]),
     (8,2,[(1,3),(7,4)]),(1,2,[(7,4),(1,3)]),(1,2,[(1,0),(1,4)]),
     (0,3,[(0,0)]),(4,0,[(7,0),(2,1)]),
     (2^128,2^129+7,[(0,3),(2^128,2^127+1)]),
     (2^128,3,[(2^129,1)]),(2^129,3,[(2^128,1)]),
     (1,2^129,[(0,0),(1,2^129),(2,1),(3,7)])]
  let mut maximum:=0
  for (index,count,edges) in cases do
    let suffix:=[true,false,false,true]
    let store : Fin 21→List Bool:=fun r=>
      if r=roles 0 then (Encoding.list edgeCodec).encode edges++suffix
      else if r=roles 1 then index.bits else if r=roles 2 then count.bits
      else if r=0 then [false,true,true,false,true] else []
    let expected:=Function.update (Function.update store (roles 0) suffix) (roles 3)
      ((Encoding.list edgeCodec).encode (Executable.addCount index count edges))
    match TestLazy.finishWithin program 2000000 0 (TestLazy.empty program) ⟨0,store⟩ with
    | none=>throw (IO.userError "complete sparse count update exceeded test fuel")
    | some (steps,finish)=>
      unless (List.finRange 21).all (fun r=>finish.store r==expected r) do
        throw (IO.userError "complete sparse count update full-store mismatch")
      unless steps ≤ 10000*((store (roles 0)).length+index.bits.length+count.bits.length+1)^3 do
        throw (IO.userError "complete sparse count update exceeded proved bound")
      maximum:=max maximum steps
  IO.println s!"DAG addCount: 16 full-store tests passed; empty/zero/insertion/merge/repeated and unsorted indices, 130-bit counts, suffix and external sentinel; maximum {maximum} instructions."

#eval tests
end Counting.StackMachine.DagUpdate.Tests
