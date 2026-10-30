import Counting.StackDagAddCountStep
import Counting.StackMachineTestLazy

namespace Counting.StackMachine.DagUpdate.StepTests

def roles : AddWorkspace 1 := ⟨fun i=>⟨i.val+1,by omega⟩,by
  intro a b h
  apply Fin.ext
  have eq:=congrArg (fun i : Fin 21=>i.val) h
  dsimp at eq
  omega⟩

def tests : IO Unit := do
  let program:=(processEdge 1 roles).program
  let mut maximum:=0
  let cases : List (Nat×Nat×Nat×Nat) :=
    [(0,0,0,0),(0,3,0,7),(0,3,1,7),(4,3,1,7),(2,0,2,9),
      (2^128,2^129+1,2^128,2^127+7),(2^128,3,2^129,1),(2^129,3,2^128,1)]
  for (index,count,i,c) in cases do
    for pending in [false,true] do
      let suffix:=[true,false,true]
      let tail:=[false,true]
      let store : Fin 21→List Bool:=fun r=>
        if r=roles 0 then edgeCodec.encode (i,c)++suffix
        else if r=roles 1 then index.bits else if r=roles 2 then count.bits
        else if r=roles 3 then [false,true,true] else if r=roles 4 then pending::tail
        else if r=roles 5 then [true,true] else if r=roles 17 then [true,false]
        else if r=roles 18 then [false,true,false] else if r=0 then [true,false,false,true] else []
      let effect:=Counting.DagUpdate.addCountStep index count pending (i,c)
      let expected:=emittedResult roles (Function.update store (roles 0) suffix) effect.1 effect.2 tail
      match TestLazy.finishWithin program 100000 0 (TestLazy.empty program) ⟨0,store⟩ with
      | none=>throw (IO.userError "sparse count step exceeded test fuel")
      | some (steps,finish)=>
        unless (List.finRange 21).all (fun r=>finish.store r==expected r) do
          throw (IO.userError "sparse count step full-store mismatch")
        maximum:=max maximum steps
  IO.println s!"DAG sparse count update: 16 full-store cases passed; all insertion branches, inactive update, zero and 130-bit counts, suffix/status/external sentinels; maximum {maximum} instructions."

#eval tests
end Counting.StackMachine.DagUpdate.StepTests
