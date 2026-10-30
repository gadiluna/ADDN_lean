import Counting.ExternalCoverNormalizeLoop
import Counting.StackMachineTestLazy

namespace Counting.External.CoverNormalization.Tests
open StackMachine CoverMachine

private def workspace : RowWorkspace 2 :=
  ⟨fun i=>⟨i.val,by omega⟩,by
    intro a b same
    exact Fin.ext (congrArg (fun r : Fin 50=>r.val) same)⟩

def loopTests : IO Unit := do
  let program := (dedupRows 2 workspace).program
  let a : MatchingVerification.RawClause := ((),0,1,2)
  let b : MatchingVerification.RawClause := ((),3,4,5)
  let c : MatchingVerification.RawClause := ((),2,1,0)
  let huge : MatchingVerification.RawClause := ((),2^128,2^128+1,2^128+2)
  let cases : List (List MatchingVerification.RawClause × List MatchingVerification.RawClause × Bool) := [
    ([],[],true),([],[a],true),([],[a,a],true),([],[a,b,a],true),
    ([] ,[a,b,a,c,b,c],true),([a],[a],true),([a],[a,b,a],true),([b],[a,b,a],true),
    ([a,b],[b,a,c,c],true),([a,a],[b,a,b],true),([],[huge,huge],true),
    ([huge],[a,huge],true),([],[a,b,a],false),([a,b],[],false)]
  let mut maximum := 0
  for (before,rows,accepted) in cases do
    let suffix := [false,true,false]
    let table := Encoding.sequence MatchingVerification.clauseCodec (before++rows)
    let store : Fin 50→List Bool := fun r=>
      if r=0 then Encoding.sequence MatchingVerification.clauseCodec rows++suffix
      else if r=1 then [accepted,false,true]
      else if r=23 then List.replicate rows.length true
      else if r=36 then [true,false,false,true]
      else if r=39 then table
      else if r=40 then List.replicate before.length true
      else if r=41 then [false,true,false]
      else if r=48 then [false,true,true]
      else if r=49 then [true,true,false] else []
    let expected := dedupResult workspace store before rows suffix
    match TestLazy.finishWithin program 3000000 0 (TestLazy.empty program) ⟨0,store⟩ with
    | none=>throw (IO.userError "deduplication loop exhausted test fuel")
    | some (steps,finish)=>
      unless (List.finRange 50).all (fun r=>finish.store r==expected r) do
        throw (IO.userError "deduplication loop full-store mismatch")
      unless steps ≤ rows.length*(2000*((store 0).length+table.length+1)^2+2)+1 do
        throw (IO.userError "deduplication loop exceeded proved bound")
      maximum := max maximum steps
  unless freshRows [] [a,b,a,c,b,c]==[a,b,c] do
    throw (IO.userError "deduplication changed first-occurrence order")
  IO.println s!"X3C deduplication: 14 full-store loop cases passed; maximum {maximum} stack transitions."

#eval loopTests
end Counting.External.CoverNormalization.Tests
