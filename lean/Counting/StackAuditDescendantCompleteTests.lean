import Counting.StackAuditDescendantComplete
import Counting.StackMachineTestSparse

namespace Counting.StackMachine.AuditDescendant.CompleteTests
open Routine

def tests : IO Unit := do
  let p:=complete.program
  let root:=Executable.initialVista true
  let next : Executable.Vista:=⟨#[⟨0,none,true,0,[]⟩,⟨1,some 0,true,0,[]⟩],1⟩
  let chain : Executable.Vista:=⟨#[⟨0,none,true,0,[]⟩,⟨1,some 0,true,0,[]⟩,
    ⟨2,some 1,true,0,[]⟩],2⟩
  let cases : List (String×Executable.Vista×Array Nat×Nat×Nat×Bool):=
    [("empty",⟨#[],0⟩,#[],0,0,true),
     ("one ancestor",root,#[1],0,0,true),
     ("zero weight",root,#[0],0,0,false),
     ("missing weight",root,#[],0,0,false),
     ("one ascent",next,#[1,0],0,1,true),
     ("one ascent rejected",next,#[0,1],0,1,false),
     ("two ascents",chain,#[1,0,0],0,2,true),
     ("zero ascent at last",chain,#[0,0,1],2,2,true),
     ("absent anchor",next,#[0,0],2^130+1,1,true),
     ("large binary weight",next,#[2^130,0],0,1,true)]
  for (name,vista,weights,anchor,last,answer) in cases do
    unless last≤vista.nodes.size && Executable.auditDescendants vista weights anchor last==answer do
      throw (IO.userError s!"Descendant fixture has unexpected specification: {name}")
    let input:=completeInputWord vista weights anchor last
    let after : Fin (p.extraRegisters+2) → List Bool := fun r => if r.val==1 then [answer] else []
    match TestSparse.finishWithin p 20000000 0 (TestSparse.empty p) (initial p input) with
    | none=>throw (IO.userError s!"Complete descendant regression exhausted fuel: {name}")
    | some (steps,finish)=>
      unless (List.finRange (p.extraRegisters+2)).all (fun r=>finish.store r==after r) do
        throw (IO.userError s!"Complete descendant answer or register cleanup mismatch: {name}")
      unless steps≤completeCoefficient*(input.length+1)^7 do
        throw (IO.userError s!"Complete descendant exceeded its proved bound: {name}")
      IO.println s!"Complete descendant {name}: {steps} instructions, answer {answer}; all 48 registers checked."
  IO.println "Ten complete descendant regressions passed."

#eval tests
end Counting.StackMachine.AuditDescendant.CompleteTests
