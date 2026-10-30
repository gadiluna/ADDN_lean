import Counting.StackAnchorCoefficient
import Counting.StackMachineTestLazy

namespace Counting.StackMachine.AnchorCoefficient.Tests

def tests : IO Unit := do
  let program := routine.program
  let cases : List (Executable.Node×Nat) :=
    [(⟨0,none,true,0,[]⟩,0), (⟨1,some 0,false,7,[(0,7)]⟩,0),
     (⟨1,some 0,false,9,[(0,7)]⟩,0), (⟨1,some 0,false,7,[(0,9)]⟩,0),
     (⟨2,some 3,true,12,[(2,0),(2,11)]⟩,2),
     (⟨4,none,false,10,[(9,3)]⟩,9),
     (⟨1,some (2^128),true,2^129,[(2^128,2^129+1)]⟩,2^128)]
  for (node,query) in cases do
    let suffix := [true,false,true]
    let previous := [false,true]
    let input := Encoding.node.encode node++suffix
    let expected := file suffix query.bits (Encoding.rational.encode (coefficient node query)++previous)
      node.level.bits [] [] [] [] [] []
    let start : Config program := ⟨0,file input query.bits previous [] [] [] [] [] [] []⟩
    match TestLazy.finishWithin program 3000000 0 (TestLazy.empty program) start with
    | none => throw (IO.userError "Anchor coefficient exhausted regression fuel")
    | some (steps,finish) =>
      unless (List.finRange 34).all (fun r=>finish.store r==expected r) do
        throw (IO.userError "Anchor coefficient or full-store cleanup differs")
      IO.println s!"Anchor coefficient {coefficient node query}: {steps} stack transitions; full store checked."
  IO.println "7 anchor coefficients passed, including negative, zero, positive, duplicate and 129-bit cases."

#eval tests
end Counting.StackMachine.AnchorCoefficient.Tests
