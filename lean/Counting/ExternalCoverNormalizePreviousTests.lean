import Counting.ExternalCoverNormalizePrevious
import Counting.StackMachineTestLazy

namespace Counting.External.CoverNormalization.PreviousTests
open StackMachine CoverMachine

private def workspace : RowWorkspace 2 :=
  ⟨fun i => ⟨i.val,by omega⟩,by
    intro a b same
    exact Fin.ext (congrArg (fun r : Fin 50 => r.val) same)⟩

def tests : IO Unit := do
  let program := (previousMembership 2 workspace).program
  let a : MatchingVerification.RawClause := ((),0,1,2)
  let b : MatchingVerification.RawClause := ((),3,4,5)
  let huge : MatchingVerification.RawClause := ((),2^128,2^128+1,2^128+2)
  let cases : List (List MatchingVerification.RawClause × Nat × MatchingVerification.RawClause) :=
    [([],0,a),([a],0,a),([a],1,a),([a],1,b),([a,b,a],0,a),([a,b,a],1,b),
      ([a,b,a],2,a),([a,b,a],2,b),([a,b,a],3,a),([huge,a],0,huge),
      ([huge,a],1,huge),([huge,a],1,a),([a,huge],1,huge),([a,huge],2,huge)]
  let mut maximum := 0
  for (rows,count,query) in cases do
    let table := Encoding.sequence MatchingVerification.clauseCodec rows
    let word := MatchingVerification.clauseCodec.encode query
    let store : Fin 50 → List Bool := fun r =>
      if r=0 then [true,false,true,false] else if r=1 then [false,true,false]
      else if r=38 then word else if r=39 then table
      else if r=40 then List.replicate count true else if r=48 then [false,true]
      else if r=49 then [true,false,false] else []
    let expected := Function.update store 22 [decide (query∈rows.take count)]
    match TestLazy.finishWithin program 1000000 0 (TestLazy.empty program) ⟨0,store⟩ with
    | none => throw (IO.userError "previous-row membership exceeded test fuel")
    | some (steps,finish) =>
      unless (List.finRange 50).all (fun r => finish.store r==expected r) do
        throw (IO.userError "previous-row membership full-store mismatch")
      unless steps ≤ 1000*((store 0).length+table.length+word.length+1)^2 do
        throw (IO.userError "previous-row membership exceeded proved bound")
      maximum := max maximum steps
  IO.println s!"X3C normalization: 14 full-store previous-row searches passed, including a match only after the cut and 129-bit indices; maximum {maximum} stack transitions."

#eval tests
end Counting.External.CoverNormalization.PreviousTests
