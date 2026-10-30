import Counting.StackAuditDescendantLevel
import Counting.StackMachineTestLazy

namespace Counting.StackMachine.AuditDescendant.LevelTests
open Routine

def tests : IO Unit := do
  let root : Executable.Node:=⟨0,none,true,0,[]⟩
  let child : Executable.Node:=⟨1,some 0,false,2,[(0,2)]⟩
  let large : Executable.Node:=⟨2^129,some (2^130),true,2^129,[(2^129,2^130)]⟩
  let nodes:=[root,child,large]
  let cases : List (Nat × Nat):=[(0,0),(0,1),(1,0),(1,1),(1,2^129),(2,0),(2,2^129),(2,2^129+1)]
  let program:=levelTest.program
  let mut maximum:=0
  for (index,last) in cases do
    let store : Store 38:=fun r=>
      if r=17 then Encoding.sequence Encoding.node nodes
      else if r=18 then List.replicate index false
      else if r=24 then [true,false,true]
      else if r=25 then [false,true]
      else if r=29 then [true,true,false]
      else if r=31 then [true,false]
      else if r=34 then last.bits
      else if r=35 then [false,true]
      else if r=39 then [true,false,false,true] else []
    let selected:=decide ((nodes[index]?.getD default).level=last)
    let expected:=Function.update (Function.update store 18 []) 35 (selected::store 35)
    match TestLazy.finishWithin program 5000000 0 (TestLazy.empty program) ⟨0,store⟩ with
    | none=>throw (IO.userError "Descendant level selection exceeded regression fuel")
    | some (time,finish)=>
      unless (List.finRange 40).all (fun r=>finish.store r==expected r) do
        throw (IO.userError "Descendant level selection full-store mismatch")
      maximum:=max maximum time
  IO.println s!"Physical descendant level selection: {cases.length} full-store tests passed; true/false comparisons, 130-bit labels, index consumption and preserved state; maximum {maximum} instructions."

#eval tests
end Counting.StackMachine.AuditDescendant.LevelTests
