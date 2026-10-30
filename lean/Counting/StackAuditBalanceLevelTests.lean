import Counting.StackAuditBalanceLevel
import Counting.StackMachineTestLazy

namespace Counting.StackMachine.AuditBalance.LevelTests

def tests : IO Unit := do
  let p:=levelLoop.program
  let root : Executable.Node:=⟨0,none,true,0,[]⟩
  let cases : List (Executable.Vista × Array Nat × Nat) :=
    [(⟨#[],0⟩,#[],0),
     (⟨#[root,⟨1,some 0,true,1,[(0,1)]⟩],1⟩,#[1,2],0),
     (⟨#[root,⟨1,some 0,true,2,[(0,1)]⟩],1⟩,#[1,2],0)]
  for (vista,weights,round) in cases do
    let saved : Fin 8→List Bool:=![
      Encoding.sequence Encoding.node vista.nodes.toList++Encoding.natural.encode vista.bottom,
      [],round.bits,[],List.replicate vista.nodes.size true,[false,true],[true,false,true],[true,true]]
    let source:=Encoding.vista.encode vista
    let values:=(Encoding.array Encoding.natural).encode weights
    let before:=bankFile source values (round+1).bits [] [true,false] saved
    let after:=bankFile source values (round+1).bits []
      [Executable.auditBalanceLevel vista weights round,false] (loopSaved saved 0 vista.nodes.size)
    match TestLazy.finishWithin p 5000000 0 (TestLazy.empty p) ⟨0,before⟩ with
    | none=>throw (IO.userError "Audit balance level exhausted regression fuel")
    | some (steps,last)=>
      unless (List.finRange (p.extraRegisters+2)).all (fun r=>last.store r==after r) do
        throw (IO.userError "Audit level status, traversal, saved-register, or cleanup mismatch")
      IO.println s!"Balance level {round}: {vista.nodes.size} nodes, {steps} transitions."
  IO.println "Three complete balance-level regressions passed; all 50 registers checked."

#eval tests
end Counting.StackMachine.AuditBalance.LevelTests
