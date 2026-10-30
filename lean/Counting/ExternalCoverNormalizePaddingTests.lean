import Counting.ExternalCoverNormalizePadding
import Counting.StackMachineTestLazy

namespace Counting.External.CoverNormalization.Tests
open StackMachine

private def workspace : EmitWorkspace 2 := ⟨![2,0,5,1,6,4],by decide⟩

def paddingTests : IO Unit := do
  let program := (emitPadding 2 workspace).program
  let mut maximum := 0
  for n in [0,1,2,3,4,6,9,12,31,32,63,64] do
    let store : Fin 8→List Bool := fun r=>
      if r=workspace 0 then List.replicate n true
      else if r=workspace 1 then [true,false,true]
      else if r=3 then [false,true,false]
      else if r=7 then [true,true,false] else []
    let expected := Function.update store (workspace 1)
      ((Encoding.sequence MatchingVerification.clauseCodec (paddingRows n)).reverse++store (workspace 1))
    match TestLazy.finishWithin program 1000000 0 (TestLazy.empty program) ⟨0,store⟩ with
    | none=>throw (IO.userError "normalization padding exhausted test fuel")
    | some (steps,finish)=>
      unless (List.finRange 8).all (fun r=>finish.store r==expected r) do
        throw (IO.userError "normalization padding full-store mismatch")
      unless steps ≤ 250*(n+6)^2 do
        throw (IO.userError "normalization padding exceeded proved bound")
      maximum := max maximum steps
  IO.println s!"X3C padding: 12 full-store cases passed; maximum {maximum} stack transitions."

#eval paddingTests
end Counting.External.CoverNormalization.Tests
