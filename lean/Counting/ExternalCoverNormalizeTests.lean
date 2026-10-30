import Counting.ExternalCoverNormalizePreserving
import Counting.X3CEncodingDeduplicate
import Counting.StackMachineTestLazy

namespace Counting.External.CoverNormalization.Tests
open StackMachine CoverMachine

private def workspace : RowWorkspace 2 :=
  ⟨fun i => ⟨i.val,by omega⟩,by
    intro a b same
    exact Fin.ext (congrArg (fun r : Fin 50 => r.val) same)⟩

def tests : IO Unit := do
  let program := (preservingMembership 2 workspace).program
  let a : MatchingVerification.RawClause := ((),0,1,2)
  let b : MatchingVerification.RawClause := ((),3,4,5)
  let c : MatchingVerification.RawClause := ((),2,1,0)
  let huge : MatchingVerification.RawClause := ((),2^128,2^128+1,2^128+2)
  let enc := MatchingVerification.clauseCodec.encode
  let cases : List (List MatchingVerification.RawClause × List Bool × Bool) := [
    ([],enc a,true),([a],enc a,true),([a],enc b,true),([a,a],enc a,true),
    ([a,b,a],enc b,true),([a,b,a],enc c,true),([c,a],enc c,true),
    ([huge,a],enc huge,true),([huge],enc a,true),([a],[],true),
    ([a],[true,false],true),([a,b],enc b,false)]
  let mut maximum := 0
  for (rows,query,accepted) in cases do
    let table := (Encoding.list MatchingVerification.clauseCodec).encode rows
    let store : Fin 50 → List Bool := fun r =>
      if r=0 then [true,false,true,false]
      else if r=1 then [accepted,false,true]
      else if r=38 then query else if r=39 then table
      else if r=40 then [false,false,true] else if r=48 then [false,true,true]
      else if r=49 then [true,true,false] else []
    let expected := Function.update store 22 [matchingRow query rows]
    match TestLazy.finishWithin program 1000000 0 (TestLazy.empty program) ⟨0,store⟩ with
    | none => throw (IO.userError "normalization row membership exceeded test fuel")
    | some (steps,finish) =>
      unless (List.finRange 50).all (fun r => finish.store r==expected r) do
        throw (IO.userError "normalization row membership full-store mismatch")
      unless steps ≤ 5000*((store 0).length+table.length+query.length+1)^3 do
        throw (IO.userError "normalization row membership exceeded proved bound")
      maximum := max maximum steps
  let rows := [a,b,a,c,b,huge,huge]
  let selected := (X3CEncoding.firstIndices (fun j : Fin rows.length => rows[j])).map Fin.val
  unless selected==[0,1,3,5] do
    throw (IO.userError "normalization first-occurrence ordering mismatch")
  IO.println s!"X3C normalization: 12 complete-store preserving membership cases and first-occurrence ordering passed; maximum {maximum} stack transitions."

#eval tests
end Counting.External.CoverNormalization.Tests
