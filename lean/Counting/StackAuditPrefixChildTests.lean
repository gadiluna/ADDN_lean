import Counting.StackAuditPrefixChildAll
import Counting.StackMachineTestLazy

namespace Counting.StackMachine.AuditPrefix.ChildTests
open Routine

def tests : IO Unit := do
  let p:=childAll.program
  let root:Executable.Node:=⟨0,none,true,0,[]⟩
  let child:Executable.Node:=⟨1,some 0,true,0,[]⟩
  let cases:List (Executable.Vista×Nat):=
    [(⟨#[],0⟩,0),(⟨#[root],0⟩,0),(⟨#[root,child],1⟩,0),
     (⟨#[root,child,{child with degree:=1}],2⟩,0)]
  for (vista,level) in cases do
    let table:=Encoding.sequence Encoding.node vista.nodes.toList++[true,false]
    let before:Store 50:=fun r=>if r=1 then [false,true] else if r=17 then table
      else if r=20 then List.replicate vista.nodes.size true else if r=30 then (level+1).bits
      else if r=41 then level.bits else if r=42 then [false,true] else if r=43 then [true,false]
      else if r=39 then [false,true,false,true] else []
    let predicates:=childRange vista level 0 vista.nodes.size
    let expected:=Function.update (Function.update before 42 (predicates.1::before 42)) 43 (predicates.2::before 43)
    match TestLazy.finishWithin p 10000000 0 (TestLazy.empty p) ⟨0,before⟩ with
    | none=>throw (IO.userError "Audit prefix child scan exhausted regression fuel")
    | some (steps,finish)=>
      unless (List.finRange 52).all (fun r=>finish.store r==expected r) do
        throw (IO.userError "Audit prefix child predicates or full-store preservation mismatch")
      unless steps≤2000000*(table.length+level.size+(level+1).size+1)^6 do
        throw (IO.userError "Audit prefix child scan exceeded its verified cost bound")
      IO.println s!"Child scan {vista.nodes.size} nodes: {steps} transitions, flags {predicates}."
  IO.println "Four complete child-scan regressions passed; all 52 registers checked."

#eval tests
end Counting.StackMachine.AuditPrefix.ChildTests
