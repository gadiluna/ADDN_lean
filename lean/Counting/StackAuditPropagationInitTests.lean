import Counting.StackAuditPropagationZero
import Counting.StackAuditPropagationAssign
import Counting.StackMachineTestLazy

namespace Counting.StackMachine.AuditPropagation.InitTests

def tests : IO Unit := do
  let p:=zeroArray.program
  for n in [0,1,2,9,33] do
    let before : Register p→List Bool :=fun r=>if r.val=0 then List.replicate n true else []
    match TestLazy.finishWithin p (80*(n+1)^2+1) 0 (TestLazy.empty p) ⟨0,before⟩ with
    | none=>throw (IO.userError "Zero-array initialization exhausted bound")
    | some (_,last)=>
      let word:=(Encoding.array Encoding.natural).encode (Array.replicate n 0)
      unless (List.finRange (p.extraRegisters+2)).all
          (fun r=>last.store r==if r.val=1 then word else before r) do
        throw (IO.userError "Zero-array initialization/store mismatch")
  let p:=assignNode.program
  for (index,value) in [(0,0),(1,7),(0,2^80)] do
    let values:=#[3,5]
    let suffix:=[true,false,true]
    let before : Register p→List Bool :=fun r=>
      if r.val=31 then List.replicate (index+1) true
      else if r.val=35 then (Encoding.array Encoding.natural).encode values
      else if r.val=36 then Encoding.natural.encode value++suffix
      else if r.val=30 then [false,true] else []
    match TestLazy.finishWithin p 1000000 0 (TestLazy.empty p) ⟨0,before⟩ with
    | none=>throw (IO.userError "Anchor assignment exhausted fuel")
    | some (_,last)=>
      let after : Register p→List Bool :=fun r=>
        if r.val=31 then [] else if r.val=35 then
          (Encoding.array Encoding.natural).encode (values.setIfInBounds index value)
        else if r.val=36 then suffix else before r
      unless (List.finRange (p.extraRegisters+2)).all (fun r=>last.store r==after r) do
        throw (IO.userError "Anchor assignment/store mismatch")
  IO.println "Five zero-array and three anchor-coordinate assignment regressions passed, all registers checked."

#eval tests
end Counting.StackMachine.AuditPropagation.InitTests
