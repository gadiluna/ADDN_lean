import Counting.ExternalCoefficientHigh
import Counting.ExternalCoefficientLoop
import Counting.StackMachineTestLazy

namespace Counting.External.CoefficientMachine.Tests
open StackMachine StackMachine.Routine
private def workspace : Workspace 2 :=
  ⟨fun i=>⟨i.val,by omega⟩,by intro a b h;exact Fin.ext (congrArg (fun i : Fin 66=>i.val) h)⟩
def tests : IO Unit := do
  let preparing:=(sequence (prepareBase 2 workspace) (prepareHigh 2 workspace)).program
  let looping:=(coefficientAtoms 2 workspace).program
  let mut maximum:=0
  for q in [0,1,2,4] do
    let store : Fin 66 → List Bool := fun r=>
      if r=17 then List.replicate (3*q) true else if r=0 then [true,false]
      else if r=1 then [false,true] else if r=64 then [true,true,false] else if r=65 then [false,true] else []
    let expected:=Function.update (Function.update (Function.update store 27 (List.replicate q true))
      52 (q+3).bits) 54 ((q+3)^(3*q)).bits
    match TestLazy.finishWithin preparing 2000000 0 (TestLazy.empty preparing) ⟨0,store⟩ with
    | none=>throw (IO.userError "coefficient base/high exceeded test fuel")
    | some (steps,finish)=>
      unless (List.finRange 66).all (fun r=>finish.store r==expected r) do
        throw (IO.userError "coefficient base/high full-store mismatch")
      maximum:=max maximum steps
  for q in [1,2,4] do
    let indices:=[0,1,3*q-1]
    let suffix:=[true,false,true]
    let base:=q+3
    let initial:=base^(3*q)
    let store : Fin 66 → List Bool := fun r=>
      if r=0 then Encoding.sequence Encoding.natural indices++suffix
      else if r=1 then [true,false] else if r=17 then List.replicate (3*q) true
      else if r=23 then List.replicate indices.length true else if r=52 then base.bits
      else if r=55 then initial.bits else if r=64 then [false,true] else if r=65 then [true,false] else []
    let expected:=Function.update (Function.update (Function.update store 23 []) 0 suffix) 55 (initial+powers base indices).bits
    match TestLazy.finishWithin looping 2000000 0 (TestLazy.empty looping) ⟨0,store⟩ with
    | none=>throw (IO.userError "coefficient atom loop exceeded test fuel")
    | some (steps,finish)=>
      unless (List.finRange 66).all (fun r=>finish.store r==expected r) do
        throw (IO.userError "coefficient atom loop full-store mismatch")
      maximum:=max maximum steps
  IO.println s!"X3C coefficient components: 7 full-store cases passed; binary base/high and indexed sum, suffix/status/sentinel preservation; maximum {maximum} stack transitions."
#eval tests
end Counting.External.CoefficientMachine.Tests
