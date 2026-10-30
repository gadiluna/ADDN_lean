import Counting.StackDagCanonicalCommitLoop
import Counting.StackMachineTestLazy

namespace Counting.StackMachine.DagUpdate.Canonical.LoopTests
open Routine

def tests : IO Unit := do
  let plain : Executable.Node := ⟨0,none,false,0,[]⟩
  let leader : Executable.Node := ⟨0,none,true,0,[]⟩
  let child : Executable.Node := ⟨1,some 0,false,2^80+3,[(0,2^80+2),(1,1)]⟩
  let cases : List (String×Executable.CanonicalState×List Sort.Record) :=
    [("empty",(#[],#[]),[]),
     ("first signature",(#[],#[0]),[(0,plain)]),
     ("reused signature",(#[plain],#[7,8]),[(1,plain)]),
     ("multiple slots",(#[],#[0,0,0,0]),[(3,plain),(1,leader),(2,plain),(0,child)]),
     ("repeated slot",(#[plain,leader],#[8,9]),[(1,plain),(1,leader)])]
  let program := commitRecords.program
  for (name,state,records) in cases do
    let suffix := [false,true,false]
    let source : Store 94 := fun r=>
      if r=1 then (Encoding.array Encoding.natural).encode state.2
      else if r=64 then (Encoding.array Encoding.node).encode state.1
      else if r=81 then [true]
      else if r=92 then (Encoding.list Sort.recordCodec).encode records++suffix
      else if r.val≤79 || r=93 then []
      else [false,true]++r.val.bits
    let expected := commitLoopResult source state records suffix
    match TestLazy.finishWithin program 10000000 0 (TestLazy.empty program) ⟨0,source⟩ with
    | none => throw (IO.userError s!"Canonical commit fold exhausted fuel: {name}")
    | some (steps,last) =>
      unless (List.finRange 96).all (fun r=>last.store r==expected r) do
        throw (IO.userError s!"Canonical commit fold output or preserved register mismatch: {name}")
      unless steps≤1820*((source 92).length+1)^3+1+commitLoopBudget state records suffix do
        throw (IO.userError s!"Canonical commit fold exceeded proved bound: {name}")
      IO.println s!"Canonical commit fold {name}: {steps} instructions; all 96 registers checked."
  IO.println "Five canonical commit fold regressions passed."

#eval tests
end Counting.StackMachine.DagUpdate.Canonical.LoopTests
