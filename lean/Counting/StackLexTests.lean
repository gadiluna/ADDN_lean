import Counting.StackLexComplete
import Counting.StackMachineTestLazy

namespace Counting.StackMachine.Lexicographic.Tests

def streamTests : IO Unit := do
  let program := compareStreams.program
  let cases : List (List Nat×List Nat) :=
    [([],[]),([],[0]),([0],[]),([0],[0]),([1],[2]),([2],[1]),
     ([1,2],[1,2,0]),([1,2,0],[1,2]),([0,9],[1,0]),([1,0],[0,9]),
     ([3,4,7],[3,4,2]),([0,0,0],[0,0,0]),
     ([2^130,1],[2^130,2]),([1,2^129],[0,2^130])]
  let mut maximum := 0
  for value in cases do
    let store : Fin 16→List Bool := fun r=>
      if r=10 then Encoding.sequence Encoding.natural value.1
      else if r=11 then Encoding.sequence Encoding.natural value.2
      else if 14≤r.val then [false,true]++r.val.bits else []
    let expected := comparisonResult store value.1 value.2
    match TestLazy.finishWithin program 2000000 0 (TestLazy.empty program) ⟨0,store⟩ with
    | none => throw (IO.userError "Lexicographic streams exceeded fuel")
    | some (steps,finish) =>
      unless (List.finRange 16).all (fun r=>finish.store r==expected r) do
        throw (IO.userError "Lexicographic streams full-store mismatch")
      unless steps≤100*((store 10).length+(store 11).length+1)^2 do
        throw (IO.userError "Lexicographic streams runtime bound mismatch")
      maximum := max maximum steps
  IO.println s!"Lexicographic numeric streams: {cases.length} full-store cases passed; maximum {maximum} instructions."

#eval streamTests
end Counting.StackMachine.Lexicographic.Tests
