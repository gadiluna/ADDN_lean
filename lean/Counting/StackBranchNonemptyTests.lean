import Counting.StackBranchNonempty
import Counting.StackMachineTestLazy

namespace Counting.StackMachine.Routine.NonemptyTests

def tests : IO Unit := do
  let yes : Routine 2:=pushBit 1 true
  let no : Routine 2:=pushBit 1 false
  let program:=(branchNonempty 0 yes no).program
  let words : List (List Bool):=[[],[false],[true],[false,true,false],[true,false,true],List.replicate 131 false]
  for word in words do
    let store : Store 2:=fun r=>if r=0 then word else if r=1 then [false,true] else [true,false]
    let expected:=Function.update store 1 ((!word.isEmpty)::store 1)
    match TestLazy.finishWithin program 10 0 (TestLazy.empty program) ⟨0,store⟩ with
    | none=>throw (IO.userError "Nonempty branch did not halt")
    | some (time,finish)=>
      unless time==(if word.isEmpty then 2 else 4) &&
          (List.finRange 4).all (fun r=>finish.store r==expected r) do
        throw (IO.userError "Nonempty branch result, exact cost or preservation mismatch")
  IO.println "Nonempty branch: six full-store tests passed, including false-leading words, both answers and exact cost."

#eval tests
end Counting.StackMachine.Routine.NonemptyTests
