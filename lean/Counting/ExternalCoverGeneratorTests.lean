import Counting.ExternalCoverGenerator
import Counting.StackMachineTestLazy

namespace Counting.External.CoverMachine.Tests
open StackMachine
private def rowWorkspace : RowWorkspace 2 :=
  ⟨fun i=>⟨i.val,by omega⟩,by intro a b h;exact Fin.ext (congrArg (fun i : Fin 50=>i.val) h)⟩
private def generatorWorkspace : MatchingMachine.GeneratorWorkspace 2 :=
  ⟨fun i=>⟨i.val,by omega⟩,by intro a b h;exact Fin.ext (congrArg (fun i : Fin 66=>i.val) h)⟩

def tests : IO Unit := do
  let loopProgram := (generateRows 2 rowWorkspace).program
  let generatorProgram := (coverGenerator 2 generatorWorkspace).program
  let mut maximum := 0
  for q in [1,3,8,17] do
    for count in [0,1,2] do
      let rows := List.replicate count [0,q-1,q/2]
      let suffix := [false,true,false]
      let store : Fin 50 → List Bool := fun r=>
        if r=0 then Encoding.sequence (Encoding.list Encoding.natural) rows++suffix
        else if r=1 then [true,false] else if r=17 then List.replicate q true
        else if r=23 then List.replicate count true else if r=36 then [true,false]
        else if r=48 then [false,true,true] else if r=49 then [false,false] else []
      let expected := rowsResult rowWorkspace store q rows suffix
      match TestLazy.finishWithin loopProgram 2000000 0 (TestLazy.empty loopProgram) ⟨0,store⟩ with
      | none => throw (IO.userError "cover row loop exceeded test fuel")
      | some (steps,finish) =>
        unless (List.finRange 50).all (fun r=>finish.store r==expected r) do
          throw (IO.userError "cover row loop disagrees with full-store contract")
        maximum := max maximum steps
  let cases : List (Nat×List (List Nat)) := [(0,[]),(1,[]),(3,[]),(1,[[0,0,0]]),
    (2,[[0,1,0],[1,0,1]]),(2,[[0,0,0],[0,0,0]]),(3,[[2,0,1]]),(8,[[7,0,3],[0,7,7]])]
  for (q,rows) in cases do
    let raw : ThreeDMEncoding.Raw := (List.replicate q true,rows)
    let source := ThreeDMEncoding.rawCodec.encode raw
    let store : Fin 66 → List Bool := fun r=>
      if r=0 then source else if r=1 then [true] else if r=17 then List.replicate q true
      else if r=25 then List.replicate rows.length true else if r=31 then [false,true]
      else if r=51 then source else if r=64 then [false,false,true] else if r=65 then [true,false] else []
    let expected := ThreeDMEncoding.rawCodec.encode (List.replicate (3*q) true,shiftedRows q rows)
    match TestLazy.finishWithin generatorProgram 4000000 0 (TestLazy.empty generatorProgram) ⟨0,store⟩ with
    | none => throw (IO.userError "cover generator exceeded test fuel")
    | some (steps,finish) =>
      unless finish.store 1==expected && finish.store 31==store 31 && finish.store 51==source &&
          finish.store 64==store 64 && finish.store 65==store 65 do
        throw (IO.userError "cover generator output or preserved data mismatch")
      maximum := max maximum steps
  IO.println s!"Matching-to-cover: 12 full-store row-loop and 8 whole-generator cases passed, including zero universe, empty families, repeated triples, boundary indices and suffix/sentinel preservation; maximum {maximum} stack transitions."
#eval tests
end Counting.External.CoverMachine.Tests
