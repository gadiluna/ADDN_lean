import Counting.StackAuditPropagationDownLoop
import Counting.StackMachineTestLazy

namespace Counting.StackMachine.AuditPropagation.DownTests

def tests : IO Unit := do
  let p:=downLoop.program
  let examples : List (Executable.Vista × Array Nat × Nat) :=
    [(⟨#[],0⟩,#[],0),
     (⟨#[⟨0,none,true,0,[]⟩],0⟩,#[9],0),
     (⟨#[⟨0,none,true,0,[]⟩,⟨1,some 0,true,0,[]⟩,⟨1,some 0,true,0,[]⟩],1⟩,#[99,3,7],1),
     (⟨#[⟨0,none,true,0,[]⟩,⟨1,some 0,true,0,[]⟩,⟨2,some 1,true,0,[]⟩],2⟩,#[99,77,11],2)]
  for (vista,weights,rounds) in examples do
    let before : Register p→List Bool:=fun i=>
      if i.val=1 then [true,false] else if i.val=17 then
        Encoding.sequence Encoding.node vista.nodes.toList++Encoding.natural.encode vista.bottom
      else if i.val=22 then rounds.bits else if i.val=34 then Encoding.vista.encode vista
      else if i.val=35 then (Encoding.array Encoding.natural).encode weights
      else if i.val=36 then List.replicate vista.nodes.size true
      else if i.val=39 then List.replicate rounds true
      else if i.val=29 then [true,false,true] else []
    match TestLazy.finishWithin p 5000000 0 (TestLazy.empty p) ⟨0,before⟩ with
    | none=>throw (IO.userError "Descending propagation exhausted fuel")
    | some (steps,last)=>
      let result:=Executable.propagateDown vista rounds weights
      let after : Register p→List Bool:=fun i=>
        if i.val=22 || i.val=39 then [] else if i.val=35 then
          (Encoding.array Encoding.natural).encode result else before i
      unless (List.finRange (p.extraRegisters+2)).all (fun i=>last.store i==after i) do
        throw (IO.userError "Descending propagation/store mismatch")
      IO.println s!"Descending propagation: {vista.nodes.size} nodes, {rounds} levels, {steps} transitions."
  IO.println "Four actual descending-loop regressions passed, including an empty DAG and all registers."

#eval tests
end Counting.StackMachine.AuditPropagation.DownTests
