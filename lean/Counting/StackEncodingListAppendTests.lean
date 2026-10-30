import Counting.StackEncodingListAppendBounds
import Counting.StackMachineTestLazy

namespace Counting.StackMachine.EncodingPrograms.AppendTests

def tests : IO Unit := do
  let program := appendCanonical.program
  let cases : List (List Nat×Nat) :=
    [([],0),([],2^129),([0],0),([1,2,3],4),([3,1,3],1),([2^130,0],2^129+7)]
  let mut maximum := 0
  for (values,value) in cases do
    let store : Fin 10→List Bool := fun r=>
      if r=0 then (Encoding.list Encoding.natural).encode values
      else if r=1 then Encoding.natural.encode value
      else if r=2 then List.replicate values.length true else []
    let expected := Function.update store 3 ((Encoding.list Encoding.natural).encode (values++[value]))
    match TestLazy.finishWithin program 1000000 0 (TestLazy.empty program) ⟨0,store⟩ with
    | none => throw (IO.userError "canonical append exceeded test fuel")
    | some (steps,finish) =>
      unless (List.finRange 10).all (fun r=>finish.store r==expected r) do
        throw (IO.userError "canonical append full-store mismatch")
      maximum := max maximum steps
  IO.println s!"Canonical list append: {cases.length} full-store tests passed, maximum {maximum} instructions."

#eval tests
end Counting.StackMachine.EncodingPrograms.AppendTests
