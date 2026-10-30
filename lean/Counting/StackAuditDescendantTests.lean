import Counting.StackAuditDescendantAll
import Counting.StackMachineTestLazy

namespace Counting.StackMachine.AuditDescendant.Tests
open Routine

def tests : IO Unit := do
  let tree : Executable.Vista:=⟨#[⟨0,none,true,0,[]⟩,⟨1,some 0,false,1,[(0,1)]⟩,
    ⟨1,some 0,true,1,[(0,1)]⟩,⟨2,some 1,false,0,[]⟩],3⟩
  let cycle : Executable.Vista:=⟨#[⟨7,some 1,false,0,[]⟩,⟨7,some 0,true,0,[]⟩],1⟩
  let large : Executable.Vista:=⟨#[⟨2^129,some (2^130),true,2^129,[(2^129,2^130)]⟩],0⟩
  let cases : List (Executable.Vista×Nat×Nat×Nat):=
    [(⟨#[],0⟩,0,0,0),(tree,0,0,0),(tree,1,1,0),(tree,2,1,0),
      (tree,1,1,1),(tree,1,2,1),(tree,2,2,0),(cycle,3,7,0),
      (large,0,2^129,0),(large,1,2^129,2^130),(large,2,2^129,0),
      (tree,2,2^129,2^130)]
  let program:=countAll.program
  let mut maximum:=0
  for (vista,steps,last,ancestor) in cases do
    let store : Store 38:=fun r=>
      if r=17 then Encoding.sequence Encoding.node vista.nodes.toList
      else if r=29 then (ancestor+1).bits
      else if r=30 then List.replicate vista.nodes.size false
      else if r=31 then [true,false]
      else if r=32 then [false,true,true]
      else if r=33 then [true,true,false]
      else if r=34 then last.bits
      else if r=38 then List.replicate steps false
      else if r=39 then [false,true] else []
    let count:=Executable.descendantCountRange vista steps last ancestor 0 vista.nodes.size
    let expected:=Function.update (Function.update store 30 []) 39 (List.replicate count true++store 39)
    match TestLazy.finishWithin program 100000000 0 (TestLazy.empty program) ⟨0,store⟩ with
    | none=>throw (IO.userError s!"Complete descendant scan exceeded regression fuel: nodes={vista.nodes.size}, steps={steps}, last={last}, ancestor={ancestor}")
    | some (time,finish)=>
      unless (List.finRange 40).all (fun r=>finish.store r==expected r) do
        throw (IO.userError "Complete descendant scan full-store mismatch")
      maximum:=max maximum time
      IO.println s!"Descendant scan case passed: nodes={vista.nodes.size}, steps={steps}, lastBits={last.size}, ancestorBits={ancestor.size}, instructions={time}"
  IO.println s!"Complete physical descendant scan: {cases.length} full-store tests passed; empty, zero-depth, branching, cycles, missing parents, 130-bit labels and preserved result tails; maximum {maximum} instructions."

#eval tests
end Counting.StackMachine.AuditDescendant.Tests
