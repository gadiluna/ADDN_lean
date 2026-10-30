import Counting.ExternalCoverNormalizePolynomial
import Counting.StackMachineTestLazy

namespace Counting.External.CoverNormalization.Tests
open StackMachine MatchingMachine

private def generatorWorkspace : GeneratorWorkspace 2 :=
  ⟨fun i=>⟨i.val+2,by omega⟩,by intro a b same;apply Fin.ext;have := congrArg (fun r : Fin 66=>r.val) same;dsimp at this;omega⟩

def generatorTests : IO Unit := do
  let w := generatorWorkspace
  let program := (generator 2 w).program
  let a : MatchingVerification.RawClause := ((),0,1,2)
  let b : MatchingVerification.RawClause := ((),3,4,5)
  let c : MatchingVerification.RawClause := ((),2,1,0)
  let huge : MatchingVerification.RawClause := ((),2^128,2^128+1,2^128+2)
  let cases : List (List Bool×List MatchingVerification.RawClause×Bool) := [
    ([],[],true),([true,true,true],[a],true),(List.replicate 6 true,[a,b],true),
    (List.replicate 6 true,[a,b,a],true),(List.replicate 9 true,[a,b,c,b,a,c],true),
    (List.replicate 3 true,[a,a,a],true),(List.replicate 6 true,[b,a,b],false),
    ([],[],false),(List.replicate 32 true,[a,b],true),
    ([false,true,false],[huge,huge],true),(List.replicate 6 true,[a,huge,a],true),
    ([],[huge,c,huge,c],false)]
  let mut maximum := 0
  for (markers,rows,accepted) in cases do
    let raw : MatchingVerification.Raw := (markers,rows)
    let input := MatchingVerification.rawCodec.encode raw
    let store : Fin 66→List Bool := fun r=>
      if r=w 0 then input else if r=w 1 then [accepted]
      else if r=w 17 then List.replicate markers.length true
      else if r=w 25 then [false,true,true]
      else if r=w 31 then [true,false,true]
      else if r=w 51 then [false,true,false,true]
      else if r=0 then [false,true,true] else if r=1 then [true,true,false] else []
    let expected := generatorResult w store raw
    match TestLazy.finishWithin program 8000000 0 (TestLazy.empty program) ⟨0,store⟩ with
    | none=>throw (IO.userError "normalization generator exhausted test fuel")
    | some (steps,result)=>
      unless (List.finRange 66).all (fun r=>result.store r==expected r) do
        throw (IO.userError "normalization generator full-store mismatch")
      unless result.store (w 1)==MatchingVerification.rawCodec.encode (normalizedRaw raw) do
        throw (IO.userError "normalization generator serialized output mismatch")
      unless steps ≤ 100000*(input.length+1)^3 do
        throw (IO.userError "normalization generator exceeded proved bound")
      maximum := max maximum steps
  IO.println s!"Complete X3C normalization generator: 12 full-store cases passed; maximum {maximum} stack transitions."

#eval generatorTests
end Counting.External.CoverNormalization.Tests
