import Counting.StackAnchorFind
import Counting.StackMachineTestLazy

namespace Counting.StackMachine.AnchorFind.Tests

def tests : IO Unit := do
  let program := lookup.program
  let cases : List (List (Nat×Nat)×Nat) :=
    [([],0),([(0,0)],0),([(0,7)],0),([(0,7)],1),([(2,9),(2,11)],2),
      ([(2,0),(2,11)],2),([(0,3),(2,5),(4,7)],4),([(0,3),(2,5),(4,7)],3),
      ([(2^128,2^129)],2^128),([(2^128,2^129)],2^128+1)]
  for (edges,query) in cases do
    let suffix := [true,false,true]
    let input := (Encoding.list edgeCodec).encode edges++suffix
    let expected := bank suffix query.bits (((edges.find? (fun e=>e.1==query)).map Prod.snd).getD 0).bits [] [] []
    let start : Config program := ⟨0,bank input query.bits [] [] [] []⟩
    match TestLazy.finishWithin program 2000000 0 (TestLazy.empty program) start with
    | none => throw (IO.userError "Sparse incoming lookup exhausted test fuel")
    | some (steps,result) =>
      unless (List.finRange 21).all (fun r=>result.store r==expected r) do
        throw (IO.userError "Sparse incoming lookup or cleanup differs")
      IO.println s!"Incoming list {edges.length}, query {query}: {steps} stack transitions; full store checked."
  IO.println "10 sparse first-match cases passed, including duplicates, zero counts, suffixes and 129-bit labels."

#eval tests
end Counting.StackMachine.AnchorFind.Tests
