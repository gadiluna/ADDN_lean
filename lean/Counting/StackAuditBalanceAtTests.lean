import Counting.StackAuditBalanceGuard
import Counting.StackMachineTestLazy

namespace Counting.StackMachine.AuditBalance.AtTests
open RealizabilityCheck

def tests : IO Unit := do
  let p:=guardAt.program
  let root : Executable.Node:=⟨0,none,true,0,[]⟩
  let balanced : Executable.Vista:=⟨#[root,⟨1,some 0,true,1,[(0,1)]⟩],1⟩
  let unbalanced : Executable.Vista:=⟨#[root,⟨1,some 0,true,2,[(0,1)]⟩],1⟩
  let cases : List (Executable.Vista × Array Nat × Nat × Bool) :=
    [(⟨#[],0⟩,#[],0,true),(⟨#[root],0⟩,#[5],0,true),
     (balanced,#[1,2],0,true),(unbalanced,#[1,2],0,true),(balanced,#[0,0],0,false)]
  for (vista,weights,parent,accepted) in cases do
    let source:=Encoding.vista.encode vista
    let values:=(Encoding.array Encoding.natural).encode weights
    let before:=massFile source values (1:Nat).bits [] parent.bits [accepted,false,true] [] [] []
    let answer:=Executable.auditBalanceAt vista weights 0 parent
    let after:=massFile source values (1:Nat).bits [] parent.bits [accepted&&answer,false,true] [] [] []
    match TestLazy.finishWithin p 5000000 0 (TestLazy.empty p) ⟨0,before⟩ with
    | none=>throw (IO.userError "Audit balance exhausted regression fuel")
    | some (steps,last)=>
      unless (List.finRange (p.extraRegisters+2)).all (fun r=>last.store r==after r) do
        throw (IO.userError "Audit balance status, preserved inputs, or cleanup mismatch")
      IO.println s!"Balance at parent {parent}: {vista.nodes.size} nodes, answer {answer}, {steps} transitions."
  IO.println "Five actual balance-guard regressions passed; all 42 registers checked."

#eval tests
end Counting.StackMachine.AuditBalance.AtTests
