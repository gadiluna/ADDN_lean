import Counting.StackUnaryDivisibleThree
import Counting.StackMachineTestLazy

namespace Counting.StackMachine.Routine.Tests
private def test (n : Nat) : IO Unit := do
  let program:=(divisibleThree (extra:=2) 0 1).program
  let store : Store 2:=fun r=>if r=0 then List.replicate n true
    else if r=1 then [false,true] else if r=2 then [true,false,true] else [false]
  let wanted:=Function.update (Function.update store 0 []) 1 (decide (n%3=0)::store 1)
  match TestLazy.finishWithin program (n+3) 0 (TestLazy.empty program) ⟨0,store⟩ with
  | none=>throw (IO.userError "Divisibility scan exhausted fuel")
  | some (time,result)=>
    unless time==n+2 && (List.finRange 4).all (fun r=>result.store r==wanted r) do
      throw (IO.userError "Divisibility scan cost or full store mismatch")

def tests : IO Unit := do
  for n in List.range 100 do test n
  for n in [1000,1001,1002] do test n
  IO.println "Divisibility by three: 103 exact-cost full-store cases passed."
#eval tests
end Counting.StackMachine.Routine.Tests
