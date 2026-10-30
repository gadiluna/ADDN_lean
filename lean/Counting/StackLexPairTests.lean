import Counting.StackLexReadPair
import Counting.StackMachineTestLazy

namespace Counting.StackMachine.Lexicographic.Tests

def tests : IO Unit := do
  let program := readPair.program
  let values : List (Nat×Nat) := [(0,0),(0,1),(1,0),(7,7),(3,11),(11,3),(2^130,2^129),(2^129,2^130)]
  let mut maximum := 0
  for value in values do
    for unresolved in [false,true] do
      for answer in [false,true] do
        let leftTail := [false,true,true]
        let rightTail := [true,false]
        let store : Fin 16→List Bool := fun r=>
          if r=2 then [unresolved]
          else if r=3 then [answer]
          else if r=10 then Encoding.natural.encode value.1++leftTail
          else if r=11 then Encoding.natural.encode value.2++rightTail
          else if 13≤r.val then [false,true]++r.val.bits else []
        let expected := readPairResult store value.1 value.2 leftTail rightTail unresolved answer
        match TestLazy.finishWithin program 100000 0 (TestLazy.empty program) ⟨0,store⟩ with
        | none => throw (IO.userError "Lexicographic pair exceeded fuel")
        | some (steps,finish) =>
          unless (List.finRange 16).all (fun r=>finish.store r==expected r) do
            throw (IO.userError "Lexicographic pair full-store mismatch")
          unless steps==readPairCost value.1 value.2 unresolved do
            throw (IO.userError "Lexicographic pair exact cost mismatch")
          maximum := max maximum steps
  IO.println s!"Lexicographic numeric pair: {4*values.length} full-store cases passed with exact cost; maximum {maximum} instructions."

#eval tests
end Counting.StackMachine.Lexicographic.Tests
