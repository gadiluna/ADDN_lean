import Counting.ExternalCoefficientGenerator
import Counting.StackMachineTestLazy

namespace Counting.External.CoefficientMachine.GeneratorTests
open StackMachine
private def workspace : Workspace 2 :=
  ⟨fun i=>⟨i.val,by omega⟩,by intro a b h;exact Fin.ext (congrArg (fun i : Fin 66=>i.val) h)⟩
def tests : IO Unit := do
  let program:=(coefficientGenerator 2 workspace).program
  let cases : List (Nat×List (List Nat)) :=
    [(0,[]),(1,[]),(1,[[0,1,2]]),(2,[]),(2,[[0,1,2],[3,4,5]]),(2,[[0,1,2],[0,1,2]])]
  let mut maximum:=0
  for (q,rows) in cases do
    let raw:X3CEncoding.Raw:=(List.replicate (3*q) true,rows)
    let store : Fin 66→List Bool := fun r=>
      if r=0 then X3CEncoding.rawCodec.encode raw else if r=1 then [true]
      else if r=17 then List.replicate (3*q) true else if r=25 then List.replicate rows.length true
      else if r=31 then [false,true] else if r=51 then [true,false,true]
      else if r=64 then [false,false,true] else if r=65 then [true,true,false] else []
    let output:=(Encoding.list Encoding.natural).encode (coefficientValues q rows)
    let expected:=Function.update (Function.update (Function.update (Function.update (Function.update store 0 [])
      1 output) 27 (List.replicate q true)) 52 (X3C.base q).bits) 54 (X3C.high q).bits
    match TestLazy.finishWithin program 5000000 0 (TestLazy.empty program) ⟨0,store⟩ with
    | none=>throw (IO.userError "coefficient whole generator exceeded fuel")
    | some (steps,finish)=>
      unless (List.finRange 66).all (fun r=>finish.store r==expected r) do
        throw (IO.userError "coefficient whole generator full-store mismatch")
      maximum:=max maximum steps
  IO.println s!"X3C coefficient whole generator: 6 full-store cases passed, empty universe/families, repeated triples and sentinel preservation; maximum {maximum} stack transitions."
#eval tests
end Counting.External.CoefficientMachine.GeneratorTests
