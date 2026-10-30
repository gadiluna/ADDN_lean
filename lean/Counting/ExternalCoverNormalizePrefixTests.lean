import Counting.ExternalCoverNormalizeBounds
import Counting.StackMachineTestLazy

namespace Counting.External.CoverNormalization.Tests
open StackMachine MatchingMachine

private def workspace : GeneratorWorkspace 2 :=
  ⟨fun i=>⟨i.val,by omega⟩,by intro a b equal;exact Fin.ext (congrArg (fun r : Fin 66=>r.val) equal)⟩

def prefixTests : IO Unit := do
  let program := (normalizePrefix 2 workspace).program
  let a : MatchingVerification.RawClause := ((),0,1,2)
  let b : MatchingVerification.RawClause := ((),3,4,5)
  let c : MatchingVerification.RawClause := ((),2,1,0)
  let huge : MatchingVerification.RawClause := ((),2^128,2^128+1,2^128+2)
  let cases : List (Nat×List MatchingVerification.RawClause×Bool) := [
    (0,[],true),(0,[a],true),(3,[a],true),(6,[a,b],true),
    (6,[a,b,a],true),(9,[a,b,c,b,a,c],true),(3,[a,a,a],true),
    (6,[b,a,b],false),(0,[],false),(32,[a,b],true),
    (3,[huge,huge],true),(6,[a,huge,a],true)]
  let mut maximum := 0
  for (u,rows,accepted) in cases do
    let raw : MatchingVerification.Raw := (List.replicate u true,rows)
    let input := MatchingVerification.rawCodec.encode raw
    let store : Fin 66→List Bool := fun r=>
      if r=0 then input else if r=1 then [accepted,false,true]
      else if r=17 then [false,true]
      else if r=25 then [true,false]
      else if r=36 then [true,false,false,true]
      else if r=41 then [false,true]
      else if r=64 then [false,true,true]
      else if r=65 then [true,true,false] else []
    let expected := prefixResult workspace store raw
    match TestLazy.finishWithin program 4000000 0 (TestLazy.empty program) ⟨0,store⟩ with
    | none=>throw (IO.userError "normalization prefix exhausted test fuel")
    | some (steps,finish)=>
      unless (List.finRange 66).all (fun r=>finish.store r==expected r) do
        throw (IO.userError "normalization prefix full-store mismatch")
      unless steps ≤ 50000*(input.length+1)^3 do
        throw (IO.userError "normalization prefix exceeded proved bound")
      maximum := max maximum steps
  IO.println s!"X3C normalization prefix: 12 full-store cases passed; maximum {maximum} stack transitions."

#eval prefixTests
end Counting.External.CoverNormalization.Tests
