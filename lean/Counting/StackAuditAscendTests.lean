import Counting.StackAuditAscendBounds
import Counting.StackMachineTestLazy

namespace Counting.StackMachine.AuditAscend.LoopTests
open Routine

def tests : IO Unit := do
  let root : Executable.Node:=⟨0,none,true,0,[]⟩
  let child : Executable.Node:=⟨1,some 0,false,2,[(0,2)]⟩
  let grandchild : Executable.Node:=⟨2,some 1,false,1,[(1,1)]⟩
  let large : Executable.Node:=⟨1,some (2^129+7),false,1,[(0,1)]⟩
  let cycle : Executable.Node:=⟨0,some 0,false,0,[]⟩
  let cases : List (List Executable.Node × Option Nat × Nat):=
    [([],some (2^129),0),([],none,3),([],some 0,1),([root],some 0,1),
      ([root,child],some 1,0),([root,child],some 1,1),([root,child],some 1,2),
      ([root,child,grandchild],some 2,2),([root,child],some (2^129),2),
      ([root,large],some 1,1),([root,large],some 1,2),([cycle],some 0,5)]
  let program:=ascendLoop.program
  let mut maximum:=0
  for (nodes,reference,steps) in cases do
    let vista : Executable.Vista:=⟨nodes.toArray,0⟩
    let bits:=(List.range steps).map (fun i=>i%2==0)
    let store : Store 30:=fun r=>
      if r=17 then Encoding.sequence Encoding.node nodes
      else if r=24 then (indexCode reference).bits
      else if r=25 then bits
      else if r=31 then [true,false,false,true] else []
    let expected:=Function.update (Function.update store 25 []) 24
      (indexCode (reference.bind (Executable.ascend vista steps))).bits
    match TestLazy.finishWithin program 30000000 0 (TestLazy.empty program) ⟨0,store⟩ with
    | none=>throw (IO.userError s!"ancestor loop exceeded test fuel: nodes={nodes.length}, steps={steps}")
    | some (time,finish)=>
      unless (List.finRange 32).all (fun r=>finish.store r==expected r) do
        throw (IO.userError "ancestor loop full-store mismatch")
      maximum:=max maximum time
  IO.println s!"Physical ancestor loop: {cases.length} full-store tests passed; zero steps, None, empty/outside, chain, cycle, 130-bit references and external sentinel; maximum {maximum} instructions."

#eval tests
end Counting.StackMachine.AuditAscend.LoopTests

