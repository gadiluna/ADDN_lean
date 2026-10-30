import Counting.StackAuditPrefixCountAll
import Counting.StackMachineTestLazy

namespace Counting.StackMachine.AuditPrefix.CountTests
open Routine

def runTests : IO Unit := do
  let root : Executable.Node:=⟨0,none,true,0,[]⟩
  let plain : Executable.Node:=⟨0,none,false,0,[]⟩
  let child : Executable.Node:=⟨1,some 0,true,2,[(0,2)]⟩
  let vista : Executable.Vista:=⟨#[root,plain,child],2⟩
  let huge:=2^80+17
  let cases : List (HeaderMode × Executable.Vista × Nat × Nat):=
    [(.level,⟨#[],0⟩,0,0),(.level,vista,0,0),(.leader,vista,0,0),
     (.child,vista,1,1),(.child,vista,1,2),(.level,⟨#[{root with level:=huge}],0⟩,huge,0)]
  for mode in [HeaderMode.level,.child,.leader] do
    let program:=(countAll mode).program
    for (kind,graph,level,parent) in cases do
      if kind=mode then
        let source:=Encoding.sequence Encoding.node graph.nodes.toList++[true,false,true]
        let before : Store 34:=fun r=>
          if r=1 then [false,true] else if r=17 then source
          else if r=20 then List.replicate graph.nodes.size true
          else if r=29 then [false,true] else if r=30 then level.bits else if r=32 then parent.bits
          else if r=21 then [true,false,false,true] else []
        let expected:=Function.update before 29
          (List.replicate (countRange graph mode level parent 0 graph.nodes.size) true++before 29)
        match TestLazy.finishWithin program 5000000 0 (TestLazy.empty program) ⟨0,before⟩ with
        | none=>throw (IO.userError "Audit prefix count exhausted regression fuel")
        | some (steps,finish)=>
          unless (List.finRange 36).all (fun r=>finish.store r==expected r) do
            throw (IO.userError "Audit prefix count or retained input/query/scratch mismatch")
          unless steps≤20000*(source.length+level.size+parent.size+1)^5 do
            throw (IO.userError "Audit prefix count exceeded its proved cost bound")
          IO.println s!"Prefix count {repr mode}: {graph.nodes.size} nodes, {steps} transitions."
  IO.println "Six prefix count regressions passed; all 36 registers checked."

#eval runTests
end Counting.StackMachine.AuditPrefix.CountTests
