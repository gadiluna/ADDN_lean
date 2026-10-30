import Counting.ExternalCoefficientBaseline
import Counting.ExternalCoefficientRows
import Counting.ExternalCoefficientHeader
import Counting.StackMachineTestLazy

namespace Counting.External.CoefficientMachine.BaselineTests
open StackMachine StackMachine.Routine
private def workspace : Workspace 2 :=
  ⟨fun i=>⟨i.val,by omega⟩,by intro a b h;exact Fin.ext (congrArg (fun i : Fin 66=>i.val) h)⟩
def tests : IO Unit := do
  let baseline:=(prepareBaseline 2 workspace).program
  let rows:=(writeCoefficientRows 2 workspace).program
  let header:=(emitCoefficientHeader 2 workspace).program
  let mut maximum:=0
  for q in [0,1,2,3] do
    let store : Fin 66 → List Bool := fun r=>
      if r=17 then List.replicate (3*q) true else if r=27 then List.replicate q true
      else if r=52 then (X3C.base q).bits else if r=54 then (X3C.high q).bits
      else if r=0 then [true,false,true] else if r=1 then [false,true]
      else if r=64 then [true,true,false] else if r=65 then [false,true] else []
    let expected:=Function.update store 55 (X3C.target q).bits
    match TestLazy.finishWithin baseline 2000000 0 (TestLazy.empty baseline) ⟨0,store⟩ with
    | none=>throw (IO.userError "coefficient baseline exceeded test fuel")
    | some (steps,finish)=>
      unless (List.finRange 66).all (fun r=>finish.store r==expected r) do
        throw (IO.userError "coefficient baseline full-store mismatch")
      maximum:=max maximum steps
  for inputRows in [[],[[0,1,2]],[[0,2,5],[1,3,4]],[[0,1,2],[0,1,2]]] do
    let suffix:=[true,false,true]
    let store : Fin 66 → List Bool := fun r=>
      if r=0 then Encoding.sequence (Encoding.list Encoding.natural) inputRows++suffix
      else if r=1 then [false,true] else if r=17 then List.replicate 6 true
      else if r=43 then List.replicate inputRows.length true else if r=52 then (5:Nat).bits
      else if r=54 then (5^6:Nat).bits else if r=36 then [true,false]
      else if r=64 then [false,true] else if r=65 then [true,false] else []
    let expected:=coefficientRowsResult workspace store 5 (5^6) inputRows suffix
    match TestLazy.finishWithin rows 2000000 0 (TestLazy.empty rows) ⟨0,store⟩ with
    | none=>throw (IO.userError "coefficient rows exceeded test fuel")
    | some (steps,finish)=>
      unless (List.finRange 66).all (fun r=>finish.store r==expected r) do
        throw (IO.userError "coefficient rows full-store mismatch")
      maximum:=max maximum steps
  for count in [0,1,7,15] do
    let store : Fin 66 → List Bool := fun r=>
      if r=25 then List.replicate count false else if r=36 then [false,true]
      else if r=1 then [false,true] else if r=64 then [false,false] else if r=65 then [true,false] else []
    let expected:=Function.update store 36 ((Encoding.natural.encode (count+1)).reverse++store 36)
    match TestLazy.finishWithin header 2000000 0 (TestLazy.empty header) ⟨0,store⟩ with
    | none=>throw (IO.userError "coefficient header exceeded test fuel")
    | some (steps,finish)=>
      unless (List.finRange 66).all (fun r=>finish.store r==expected r) do
        throw (IO.userError "coefficient header full-store mismatch")
      maximum:=max maximum steps
  IO.println s!"X3C coefficient baseline/rows/header: 12 full-store cases passed; empty and repeated families, suffix/status/sentinels preserved; maximum {maximum} stack transitions."
#eval tests
end Counting.External.CoefficientMachine.BaselineTests
