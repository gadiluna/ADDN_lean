import Counting.StackAuditPropagationStep
import Counting.StackMachineTestLazy

namespace Counting.StackMachine.AuditPropagation.Tests

def tests : IO Unit := do
  let p:=updateNode.program
  let examples : List (Executable.Vista × Array Nat × Nat × Nat) :=
    [(⟨#[⟨0,none,true,0,[]⟩],0⟩,#[9],0,0),
     (⟨#[⟨0,none,true,0,[]⟩,⟨1,some 0,true,0,[]⟩,⟨1,some 0,true,0,[]⟩],1⟩,#[99,3,7],0,0),
     (⟨#[⟨0,none,true,0,[]⟩,⟨1,some 0,true,0,[]⟩,⟨2,some 0,true,0,[]⟩],2⟩,#[99,3,7],0,0),
     (⟨#[⟨0,none,true,0,[]⟩,⟨1,some 0,true,0,[]⟩],1⟩,#[99,2^80],0,0)]
  for (vista,weights,r,old) in examples do
    let before : Register p→List Bool :=fun i=>
      if i.val=1 then [true] else if i.val=22 then (r+1).bits else if i.val=25 then (old+1).bits
      else if i.val=31 then List.replicate (old+1) true else if i.val=34 then Encoding.vista.encode vista
      else if i.val=35 then (Encoding.array Encoding.natural).encode weights
      else if i.val=30 then [false,true] else []
    match TestLazy.finishWithin p 2000000 0 (TestLazy.empty p) ⟨0,before⟩ with
    | none=>throw (IO.userError "Propagation node update exhausted fuel")
    | some (steps,last)=>
      let result:=weights.setIfInBounds old (RealizabilityVerifier.childCount vista weights r old)
      let after : Register p→List Bool :=fun i=>if i.val=31 then [] else if i.val=35 then
        (Encoding.array Encoding.natural).encode result else before i
      unless (List.finRange (p.extraRegisters+2)).all (fun i=>last.store i==after i) do
        throw (IO.userError "Propagation node update or preserved registers mismatch")
      IO.println s!"Propagation update with {vista.nodes.size} nodes: {steps} transitions; all registers checked."
  IO.println "Four actual child-sum/serialized-update regressions passed."

#eval tests
end Counting.StackMachine.AuditPropagation.Tests
