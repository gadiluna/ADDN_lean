import Counting.StackAuditPropagationAnchorLoop
import Counting.StackMachineTestLazy

namespace Counting.StackMachine.AuditPropagation.AnchorTests

def tests : IO Unit := do
  let p:=anchorLoop.program
  let root : Executable.Node:=⟨0,none,true,0,[]⟩
  let child : Executable.Node:=⟨1,some 0,true,0,[]⟩
  let cases : List (List Executable.Node × Nat × List Nat) :=
    [([],0,[]),([root],0,[7]),([root,child],1,[3]),
     ([root,child,child],1,[5]),([root,child],1,[5,9]),([root],3,[2^80])]
  for (nodes,anchor,values) in cases do
    let weights:=Array.replicate nodes.length 0
    let table:=Encoding.sequence Encoding.node nodes
    let before : Register p→List Bool:=fun r=>
      if r.val=1 then [true,false] else if r.val=17 then table
      else if r.val=30 then anchor.bits else if r.val=32 then List.replicate nodes.length true
      else if r.val=35 then (Encoding.array Encoding.natural).encode weights
      else if r.val=36 then Encoding.sequence Encoding.natural values
      else if r.val=33 then [true,false,true] else []
    match TestLazy.finishWithin p 1000000 0 (TestLazy.empty p) ⟨0,before⟩ with
    | none=>throw (IO.userError "Anchor assignment loop exhausted fuel")
    | some (steps,last)=>
      let result:=assignScan anchor 0 nodes values weights
      let after : Register p→List Bool:=fun r=>
        if r.val=18 then List.replicate nodes.length true else if r.val=32 then []
        else if r.val=35 then (Encoding.array Encoding.natural).encode result
        else if r.val=36 then Encoding.sequence Encoding.natural (remainingValues anchor nodes values)
        else before r
      unless (List.finRange (p.extraRegisters+2)).all (fun r=>last.store r==after r) do
        throw (IO.userError "Anchor assignment loop/store mismatch")
      IO.println s!"Anchor loop: {nodes.length} nodes, anchor {anchor}, {values.length} values, {steps} transitions."
  IO.println "Six actual anchor-loop regressions passed; short/excess vectors and all registers checked."

#eval tests
end Counting.StackMachine.AuditPropagation.AnchorTests
