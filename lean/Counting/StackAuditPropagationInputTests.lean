import Counting.StackAuditPropagationInput
import Counting.StackMachineTestLazy

namespace Counting.StackMachine.AuditPropagation.InputTests

def tests : IO Unit := do
  let p:=preparePropagationInput.program
  let root : Executable.Vista:=⟨#[⟨0,none,true,0,[]⟩],0⟩
  let cases : List (Nat × Executable.Vista × Array Nat) :=
    [(0,⟨#[],0⟩,#[]),(0,root,#[]),(0,root,#[0]),(1,root,#[2^80]),
     (0,⟨#[⟨0,none,false,0,[]⟩,⟨1,some 0,false,2^40,[(0,2^40)]⟩],1⟩,#[1,0,2^80])]
  for (anchor,vista,values) in cases do
    let word:=propagationInputWord anchor vista values
    let before : Register p→List Bool:=fun r=>if r.val=0 then word else []
    match TestLazy.finishWithin p 2000000 0 (TestLazy.empty p) ⟨0,before⟩ with
    | none=>throw (IO.userError "Propagation input exhausted fuel")
    | some (steps,last)=>
      let expected:=propagationSetupFile anchor vista values
      unless (List.finRange (p.extraRegisters+2)).all (fun r=>last.store r==expected r) do
        throw (IO.userError "Propagation input/full store mismatch")
      IO.println s!"Propagation input: {vista.nodes.size} nodes, {values.size} values, {steps} transitions."
  IO.println "Five actual propagation-input regressions passed; all 44 registers checked."

#eval tests
end Counting.StackMachine.AuditPropagation.InputTests
