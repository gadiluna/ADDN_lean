import Counting.StackDagParentRemap
import Counting.StackMachineTestLazy

namespace Counting.StackMachine.DagUpdate.ParentTests
open Routine

def tests : IO Unit := do
  let program:=remapParent.program
  let cases : List (List Nat × Nat) :=
    [([],0),([],1),([7],0),([7],1),([0],1),([7,9],2),
      ([7,9],3),([2^128+3,0,5],1),([2^128+3,0,5],2),
      ([2^128+3,0,5],3),([7,9],2^129+1),([],2^129)]
  let mut maximum:=0
  for (mapping,code) in cases do
    let store : Store 18:=fun r=>
      if r=0 then (Encoding.list Encoding.natural).encode mapping
      else if r=1 then code.bits else []
    let expected:=Function.update store 2 (remapParentCode mapping code).bits
    match TestLazy.finishWithin program 20000000 0 (TestLazy.empty program) ⟨0,store⟩ with
    | none=>throw (IO.userError s!"parent remapping exceeded test fuel: length={mapping.length}, code={code}")
    | some (steps,finish)=>
      unless (List.finRange 20).all (fun r=>finish.store r==expected r) do
        throw (IO.userError "parent remapping full-store mismatch")
      maximum:=max maximum steps
  IO.println s!"DAG parent remapping: {cases.length} full-store tests passed; None, Some0, missing references, 130-bit indices, 129-bit results; maximum {maximum} instructions."

#eval tests
end Counting.StackMachine.DagUpdate.ParentTests
