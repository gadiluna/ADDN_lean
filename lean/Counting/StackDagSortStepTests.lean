import Counting.StackDagSortStep
import Counting.StackMachineTestLazy

namespace Counting.StackMachine.DagUpdate.Sort.Tests

def stepTests : IO Unit := do
  let program := insertionStep.program
  let zero : Executable.Node := ⟨0,none,false,0,[]⟩
  let leader : Executable.Node := ⟨0,none,true,0,[]⟩
  let big : Executable.Node := ⟨2^128,some (2^129),true,2^130,[(2^127,2^130)]⟩
  let cases : List (Record×Record) := [((7,zero),(3,leader)),((0,leader),(8,zero)),((11,zero),(9,zero)),((2^129,big),(3,zero))]
  let mut maximum := 0
  for value in cases do
    for inserted in [false,true] do
      let suffix := [false,true,false]
      let store : Fin 96→List Bool := fun r=>
        if r=80 then recordCodec.encode value.2++suffix
        else if r=64 then Encoding.node.encode value.1.2
        else if r=82 then recordCodec.encode value.1
        else if r=81 then [true]
        else if r=84 then [inserted]
        else if r.val≤14 || (40≤r.val && r.val≤44) || (49≤r.val && r.val≤51) ||
          r=65 || r=66 || r=67 || r=86 || r=88 || r=89 then []
        else [true,false]++r.val.bits
      let expected := insertionStepResult store value.1 value.2 suffix inserted
      match TestLazy.finishWithin program 5000000 0 (TestLazy.empty program) ⟨0,store⟩ with
      | none => throw (IO.userError "DAG insertion step exceeded fuel")
      | some (steps,finish) =>
        unless (List.finRange 96).all (fun r=>finish.store r==expected r) do
          throw (IO.userError "DAG insertion step full-store mismatch")
        maximum := max maximum steps
  IO.println s!"DAG insertion step: {2*cases.length} full-store cases passed; maximum {maximum} instructions."

#eval stepTests
end Counting.StackMachine.DagUpdate.Sort.Tests
