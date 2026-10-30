import Counting.ExternalCoverUniverseLoop
import Counting.StackMachineTestLazy

namespace Counting.External.CoverVerification.LoopTests
open StackMachine
private def workspace : CoverMachine.RowWorkspace 2 :=
  ⟨fun i=>⟨i.val,by omega⟩,by intro a b h;exact Fin.ext (congrArg (fun i : Fin 50=>i.val) h)⟩

def tests : IO Unit := do
  let program := (universeLoop 2 workspace).program
  let cases : List (Nat×List (List Nat)×List Bool) := [
    (0,[],[]),(3,[],[]),(3,[[0,1,2]],[true]),(3,[[0,1,2]],[false]),
    (3,[[0,1,2],[0,1,2]],[true,false]),(3,[[0,1,2],[0,1,2]],[true,true]),
    (6,[[0,1,2],[3,4,5]],[true,true]),(6,[[0,1,2],[3,4,5]],[true,false]),
    (6,[[0,1,2],[2,3,4]],[true,true]),(3,[[0,1,2],[0,1,2]],[false,true])]
  let mut maximum := 0
  for (count,rows,mask) in cases do
    for accepted in [false,true] do
      let store : Fin 50 → List Bool := fun r=>
        if r=1 then [accepted,false,true] else if r=25 then List.replicate rows.length true
        else if r=33 then mask else if r=34 then Encoding.sequence (Encoding.list Encoding.natural) rows
        else if r=42 then List.replicate count true else if r=48 then [true,false,true]
        else if r=49 then [false,false] else []
      let expected := universeResult workspace store rows mask 0 count accepted [false,true]
      match TestLazy.finishWithin program 2000000 0 (TestLazy.empty program) ⟨0,store⟩ with
      | none => throw (IO.userError "cover universe audit exceeded test fuel")
      | some (steps,finish) =>
        unless (List.finRange 50).all (fun r=>finish.store r==expected r) do
          throw (IO.userError "cover universe audit full-store mismatch")
        maximum := max maximum steps
  IO.println s!"X3C universe audit: 20 full-store cases passed; empty universe/families, positive/negative masks, duplicate coverage and preserved tails/sentinels; maximum {maximum} stack transitions."
#eval tests
end Counting.External.CoverVerification.LoopTests
