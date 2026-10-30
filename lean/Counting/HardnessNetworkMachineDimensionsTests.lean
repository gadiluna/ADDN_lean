import Counting.HardnessNetworkMachineDimensions
import Counting.StackMachineTestLazy

namespace Counting.StackMachine.HardnessNetworkDimensions.Tests

def tests : IO Unit := do
  let p:=routine.program
  for (q,m) in [(0,0),(0,5),(1,0),(1,2),(3,4),(12,17)] do
    let before : Register p→List Bool :=fun r=>
      if r.val=0 then List.replicate q true else if r.val=1 then List.replicate m true
      else if r.val=6 then [false,true,false] else []
    match TestLazy.finishWithin p (cost q m+1) 0 (TestLazy.empty p) ⟨0,before⟩ with
    | none=>throw (IO.userError "Dimension routine failed exact fuel")
    | some (steps,last)=>
      let after : Register p→List Bool :=fun r=>
        if r.val=2 then List.replicate (q+3) true
        else if r.val=3 then List.replicate (2+(m+1)*(q+3)) true else before r
      unless steps==cost q m && (List.finRange (p.extraRegisters+2)).all (fun r=>last.store r==after r) do
        throw (IO.userError "Dimension result/store/exact-cost mismatch")
  IO.println "Six network-dimension regressions passed: exact costs, all seven registers, preserved sentinel."

#eval tests
end Counting.StackMachine.HardnessNetworkDimensions.Tests
