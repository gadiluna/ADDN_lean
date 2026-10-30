import Counting.StackAnchorRow
import Counting.StackMachineTestLazy

namespace Counting.StackMachine.AnchorRow.Tests

def tests : IO Unit := do
  let program := row.program
  let nodes : List Executable.Node := [⟨0,none,true,0,[]⟩,
    ⟨1,some 0,false,3,[(0,2)]⟩,⟨1,some 0,true,2,[(0,5)]⟩,
    ⟨2,some 1,false,0,[(1,0),(1,7)]⟩]
  let cases : List (List Executable.Node×Nat×Nat) :=
    [([],0,0),(nodes,0,0),(nodes,0,1),(nodes,1,2),(nodes,0,7),
      ([⟨1,some (2^128),true,2^129,[(2^128,2^129+1)]⟩],2^128,1)]
  for (current,query,anchor) in cases do
    let suffix := [true,false,true]
    let input := Encoding.sequence Encoding.node current++suffix
    let expected := file suffix query.bits anchor.bits
      (Encoding.rationalRow.encode (AnchorCoefficient.flowRow current anchor query)) [] [] [] [] []
    let start : Config program := ⟨0,file input query.bits anchor.bits [] [] [] []
      (List.replicate current.length true) []⟩
    match TestLazy.finishWithin program 5000000 0 (TestLazy.empty program) start with
    | none => throw (IO.userError "Anchor flow row exhausted regression fuel")
    | some (steps,finish) =>
      unless (List.finRange 40).all (fun r=>finish.store r==expected r) do
        throw (IO.userError "Anchor flow row differs from the ordered filtered matrix row")
      IO.println s!"Anchor {anchor}, parent {query}, nodes {current.length}: {steps} transitions; all registers checked."
  IO.println "Six full anchor row cases passed, including anchor zero, missing level, duplicate zero and 129-bit labels."

#eval tests
end Counting.StackMachine.AnchorRow.Tests
