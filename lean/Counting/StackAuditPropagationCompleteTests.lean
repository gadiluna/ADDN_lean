import Counting.StackAuditPropagationComplete
import Counting.StackMachineTestLazy

namespace Counting.StackMachine.AuditPropagation.CompleteTests

def tests : IO Unit := do
  let p:=completePropagation.program
  let root : Executable.Vista:=⟨#[⟨0,none,true,0,[]⟩],0⟩
  let branching : Executable.Vista:=⟨#[⟨0,none,true,0,[]⟩,
    ⟨1,some 0,true,0,[]⟩,⟨1,some 0,true,0,[]⟩],1⟩
  let chain : Executable.Vista:=⟨#[⟨0,none,true,0,[]⟩,
    ⟨1,some 0,true,0,[]⟩,⟨2,some 1,true,0,[]⟩],2⟩
  let cases : List (Nat × Executable.Vista × Array Nat) :=
    [(0,⟨#[],0⟩,#[]),(0,root,#[]),(0,root,#[0,2^40]),
     (1,branching,#[3,7]),(2,chain,#[11])]
  for (anchor,vista,values) in cases do
    let word:=propagationInputWord anchor vista values
    let expected:=propagationOutputWord anchor vista values
    match TestLazy.finishWithin p 5000000 0 (TestLazy.empty p) (initial p word) with
    | none=>throw (IO.userError "Complete propagation exhausted regression fuel")
    | some (steps,last)=>
      unless (List.finRange (p.extraRegisters+2)).all (fun r=>
          last.store r==if r.val=1 then expected else []) do
        throw (IO.userError "Complete propagation output or cleanup mismatch")
      IO.println s!"Complete propagation: anchor {anchor}, {vista.nodes.size} nodes, {steps} transitions."
  IO.println "Five complete propagation regressions passed, including exact cleanup of all 44 registers."

#eval tests
end Counting.StackMachine.AuditPropagation.CompleteTests
