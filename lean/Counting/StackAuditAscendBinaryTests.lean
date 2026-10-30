import Counting.StackAuditAscendBinary
import Counting.StackMachineTestLazy

namespace Counting.StackMachine.AuditAscend.Tests
open Routine

def tests : IO Unit := do
  let root : Executable.Node:=⟨0,none,true,0,[]⟩
  let child : Executable.Node:=⟨1,some 0,false,2,[(0,2)]⟩
  let large : Executable.Node:=⟨2^80,some (2^129+7),false,2^90,[(0,2^85)]⟩
  let cases : List (List Executable.Node × Nat):=
    [([],0),([],2^129),([root],0),([root],1),([root,child],1),
      ([root,child],2),([root,child],2^129),([root,large,child],1),
      ([root,large,child],2),([root,large,child],3)]
  let program:=binaryParentAt.program
  let mut maximum:=0
  for (nodes,index) in cases do
    let store : Store 22:=fun r=>
      if r=17 then Encoding.sequence Encoding.node nodes
      else if r=21 then Encoding.natural.encode index else []
    let expected:=Function.update store 2 (DagValidation.parentCode (nodes[index]?.getD default)).bits
    match TestLazy.finishWithin program 20000000 0 (TestLazy.empty program) ⟨0,store⟩ with
    | none=>throw (IO.userError s!"binary parent read exceeded test fuel: nodes={nodes.length}, index={index}")
    | some (steps,finish)=>
      unless (List.finRange 24).all (fun r=>finish.store r==expected r) do
        throw (IO.userError "binary parent read full-store mismatch")
      maximum:=max maximum steps
  IO.println s!"Binary DAG parent read: {cases.length} full-store tests passed; empty/outside/missing parent, Some0, 130-bit query and parent; maximum {maximum} instructions."

#eval tests
end Counting.StackMachine.AuditAscend.Tests

