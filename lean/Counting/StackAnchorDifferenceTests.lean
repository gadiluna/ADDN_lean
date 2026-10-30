import Counting.StackAnchorDifference
import Counting.StackMachineTestLazy

namespace Counting.StackMachine.AnchorDifference.Tests

def tests : IO Unit := do
  let program := difference.program
  for (first,second) in ([(0,0),(0,1),(1,0),(7,9),(9,7),(12,12),(2^128,2^128+1)] : List (Nat×Nat)) do
    let suffix := [false,true,false]
    let expected := file [] [] [] [] (Encoding.rational.encode ((first:Rat)-second)++suffix)
    match TestLazy.finishWithin program 2000000 0 (TestLazy.empty program)
        (⟨0,file first.bits second.bits [] [] suffix⟩ : Config program) with
    | none => throw (IO.userError "Anchor difference exhausted fuel")
    | some (steps,result) =>
      unless (List.finRange 16).all (fun r=>result.store r==expected r) &&
          steps≤10000*(first.size+second.size+1) do
        throw (IO.userError "Anchor difference value, cleanup or proved bound differs")
      IO.println s!"Anchor difference {first}-{second}: {steps} transitions, full store and bound checked."
  IO.println "Seven binary anchor-difference regressions passed."

#eval tests
end Counting.StackMachine.AnchorDifference.Tests
