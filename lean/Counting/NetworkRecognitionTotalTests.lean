import Counting.NetworkRecognitionTotal
import Counting.StackMachineTestLazy

namespace Counting.StackMachine.NetworkRecognition.TotalTests
open Routine

private def requireRun (name:String) (input:List Bool) (expected:Bool) : IO Nat := do
  unless validNetworkWord input==expected do
    throw (IO.userError s!"Network reference case disagrees with expected result: {name}")
  let program:=totalNetworkCheck.program
  match TestLazy.finishWithin program 3000000 0 (TestLazy.empty program) ⟨0,inputStore 24 input⟩ with
  | none=>throw (IO.userError s!"Total network validator exhausted fuel: {name}")
  | some (time,result)=>
    unless result.store 1==[expected] do
      throw (IO.userError s!"Total network validator disagreed: {name}")
    return time

def tests : IO Unit := do
  let singleton:Simulation.Input:=⟨#[true],#[#[#[0]]]⟩
  let good:Simulation.Input:=⟨#[true,false],#[#[#[0,2^129],#[1,0]],#[#[1,3],#[2,0]]]⟩
  let noLeaders:Simulation.Input:=⟨#[false,false],#[#[#[0,1],#[1,0]]]⟩
  let badRow:Simulation.Input:=⟨#[true,false],#[#[#[0],#[1,0]]]⟩
  let badMatrix:Simulation.Input:=⟨#[true,false],#[#[#[0,1]]]⟩
  let disconnected:Simulation.Input:=⟨#[true,false],#[#[#[2,0],#[0,3]]]⟩
  let cases:List (String×List Bool×Bool):=[
    ("empty raw input",[],false),
    ("truncated raw input",[true],false),
    ("empty agent universe",Encoding.networkInput.encode ⟨#[],#[]⟩,false),
    ("leader missing",Encoding.networkInput.encode noLeaders,false),
    ("singleton zero arcs",Encoding.networkInput.encode singleton,true),
    ("two valid varying rounds with large multiplicity",Encoding.networkInput.encode good,true),
    ("short row",Encoding.networkInput.encode badRow,false),
    ("short matrix",Encoding.networkInput.encode badMatrix,false),
    ("disconnected round",Encoding.networkInput.encode disconnected,false),
    ("trailing suffix",Encoding.networkInput.encode singleton++[true],false),
    ("zero rounds",Encoding.networkInput.encode ⟨#[false,true],#[]⟩,true)]
  let mut maximum:=0
  for (name,input,expected) in cases do
    let time ← requireRun name input expected
    maximum:=max maximum time
  IO.println s!"Total network validator passed {cases.length} end-to-end cases; maximum {maximum} instructions."

#eval tests
end Counting.StackMachine.NetworkRecognition.TotalTests
