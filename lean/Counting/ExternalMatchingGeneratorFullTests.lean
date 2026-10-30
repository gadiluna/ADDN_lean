import Counting.ExternalMatchingGenerator
import Counting.ExternalThreeDMEncoding
import Counting.StackMachineTestMemo

namespace Counting.External.MatchingMachine.FullTests
open StackMachine
private def workspace : GeneratorWorkspace 2 :=
  ⟨fun i=>⟨i.val,by omega⟩,by intro a b h;exact Fin.ext (congrArg (fun i : Fin 66=>i.val) h)⟩

def tests : IO Unit := do
  let program := TestRun.tabulate (matchingGenerator 2 workspace).program
  let cases : List (Nat×List (List (Nat×Bool))) := [
    (0,[]),(1,[]),(2,[]),(1,[[(0,true),(0,true),(0,true)]]),
    (1,[[(0,false),(0,true),(0,false)]]),
    (1,[[(0,true),(0,true),(0,true)],[(0,false),(0,false),(0,false)]]),
    (2,[[(0,false),(1,true),(0,true)]]),
    (2,[[(1,false),(0,true),(1,false)]])]
  let mut maximum := 0
  for (n,clauses) in cases do
    let raw : CNFEncoding.Raw := (List.replicate n true,clauses)
    let source := CNFEncoding.rawCodec.encode raw
    let store : Fin 66 → List Bool := fun r=>
      if r=0 then source else if r=1 then [true] else if r=17 then List.replicate n true
      else if r=25 then List.replicate clauses.length true else if r=31 then [false,true]
      else if r=51 then source else if r=64 then [false,false,true] else if r=65 then [true,false] else []
    let expected := ThreeDMEncoding.rawCodec.encode
      (List.replicate (MatchingDimensions.order n clauses.length) true,matchingRows n clauses)
    match TestRun.finishWithin program 4000000 ⟨0,store⟩ with
    | none => throw (IO.userError "complete matching generator exceeded test fuel")
    | some (steps,finish) =>
      unless finish.store 1==expected && finish.store 31==store 31 && finish.store 51==source &&
          finish.store 64==store 64 && finish.store 65==store 65 do
        throw (IO.userError "complete matching generator output or preserved data mismatch")
      maximum := max maximum steps
  IO.println s!"Complete matching generator: 8 canonical formulas passed; empty and unused-variable instances, both signs, unsatisfiable opposite clauses and external sentinels; maximum {maximum} actual stack transitions."
#eval tests
end Counting.External.MatchingMachine.FullTests
