import Counting.StackAuditDescendantCheck
import Counting.StackMachineTestLazy

namespace Counting.StackMachine.AuditDescendant.CheckTests
open Routine

def tests : IO Unit := do
  let root : Executable.Vista:=⟨#[⟨0,none,true,0,[]⟩],0⟩
  let child : Executable.Vista:=⟨#[⟨0,none,true,0,[]⟩,⟨1,some 0,true,0,[]⟩],1⟩
  let cases : List (Executable.Vista×Array Nat×Nat×Nat×Nat):=
    [(⟨#[],0⟩,#[],0,0,0),(root,#[1],0,0,0),(root,#[0],0,0,0),
      (child,#[1,1],0,1,0),(child,#[0,1],0,1,0),(child,#[],0,1,0),
      (child,#[2^129],0,1,0),(child,#[1],0,1,2^130)]
  let program:=checkAncestor.program
  let mut maximum:=0
  for (vista,weights,anchor,last,ancestor) in cases do
    let store : Store 38:=fun r=>
      if r=17 then (Encoding.array Encoding.node).encode vista.nodes
      else if r=29 then (ancestor+1).bits
      else if r=32 then (Encoding.array Encoding.natural).encode weights
      else if r=33 then Encoding.natural.encode ancestor
      else if r=34 then last.bits
      else if r=38 then List.replicate (last-anchor) false else []
    let expected:=Function.update
      (Function.update store 17 (Encoding.sequence Encoding.node vista.nodes.toList)) 35
      [Executable.auditDescendantAt vista weights anchor last ancestor]
    match TestLazy.finishWithin program 20000000 0 (TestLazy.empty program) ⟨0,store⟩ with
    | none=>throw (IO.userError s!"Descendant inequality exceeded regression fuel: nodes={vista.nodes.size}, ancestorBits={ancestor.size}")
    | some (time,finish)=>
      unless (List.finRange 40).all (fun r=>finish.store r==expected r) do
        throw (IO.userError "Descendant inequality full-store mismatch")
      maximum:=max maximum time
      IO.println s!"Descendant inequality case passed in {time} instructions."
  IO.println s!"Physical descendant inequality: {cases.length} full-store tests passed; both answers, default-zero weights, 130-bit weights and queries, complete scratch cleanup; maximum {maximum} instructions."

#eval tests
end Counting.StackMachine.AuditDescendant.CheckTests
