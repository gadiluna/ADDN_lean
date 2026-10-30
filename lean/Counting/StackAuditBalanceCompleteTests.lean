import Counting.StackAuditBalancePolynomial
import Counting.StackMachineTestLazy

namespace Counting.StackMachine.AuditBalance.CompleteTests
open Routine

def tests : IO Unit := do
  let p:=completeBalance.program
  let root : Executable.Node:=⟨0,none,true,0,[]⟩
  let cases : List (Nat × Executable.Vista × Array Nat) :=
    [(0,⟨#[],0⟩,#[]),
     (1,⟨#[root],0⟩,#[5]),
     (2,⟨#[root,⟨1,some 0,true,1,[(0,1)]⟩],1⟩,#[1,2]),
     (2,⟨#[root,⟨1,some 0,true,2,[(0,1)]⟩],1⟩,#[1,2])]
  for (anchor,vista,weights) in cases do
    let input:=balanceInputWord anchor vista weights
    let before:=inputStore 48 input
    let after:=outputStore 48 [Executable.auditBalance vista weights anchor]
    match TestLazy.finishWithin p 10000000 0 (TestLazy.empty p) ⟨0,before⟩ with
    | none=>throw (IO.userError "Complete balance check exhausted regression fuel")
    | some (steps,last)=>
      unless (List.finRange (p.extraRegisters+2)).all (fun r=>last.store r==after r) do
        throw (IO.userError "Complete balance decision or full-store cleanup mismatch")
      unless steps≤balanceCoefficient*(input.length+1)^17 do
        throw (IO.userError "Complete balance exceeded its verified polynomial bound")
      IO.println s!"Complete balance anchor {anchor}: {vista.nodes.size} nodes, {steps} transitions, result {Executable.auditBalance vista weights anchor}."
  IO.println "Four complete balance regressions passed; all 50 registers checked."

#eval tests
end Counting.StackMachine.AuditBalance.CompleteTests
