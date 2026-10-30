import Counting.NetworkRecognitionMachine
import Counting.MachineTestMemo

namespace Counting.Machine.NetworkRecognitionTests
open StackMachine.NetworkRecognition

def tests : IO Unit := do
  let singleton:Simulation.Input:=⟨#[true],#[#[#[0]]]⟩
  let cases:List (List Bool×Bool):=[([],false),(Encoding.networkInput.encode singleton,true)]
  for (input,expected) in cases do
    let program:=networkValidationMachine
    match TestMemo.finishWithin program 30000000 0 (TestMemo.empty program) (initial program input) with
    | none=>throw (IO.userError "Physical network validator exceeded fuel")
    | some (steps,finish)=>
      let right:=finish.tape.head::finish.tape.right
      unless finish.tape.left.all (· == .blank) && right.take 1==[bitSymbol expected] &&
          (right.drop 1).all (· == .blank) do
        throw (IO.userError "Physical network validator has wrong output or dirty tape")
      IO.println s!"Network validator physical run: {steps} transitions, exact clean output."

#eval tests
end Counting.Machine.NetworkRecognitionTests
