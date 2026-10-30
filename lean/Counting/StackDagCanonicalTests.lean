import Counting.MachineDagSortComplete
import Counting.StackDagCanonicalCommit
import Counting.StackMachineTestLazy

namespace Counting.StackMachine.DagUpdate.Canonical.Tests

def tests : IO Unit := do
  let zero : Executable.Node:=⟨0,none,false,0,[]⟩
  let leader : Executable.Node:=⟨0,none,true,0,[]⟩
  let child : Executable.Node:=⟨1,some 0,false,2^65,[(0,2^64),(1,1)]⟩
  let cases : List (List Sort.Record):=
    [[],[(0,zero)],[(3,leader),(9,zero)],[(7,zero),(8,zero),(2,leader)],[(2^65,child),(1,zero)]]
  let mut maximum:=0
  let program:=Sort.completeSort.program
  for records in cases do
    let source:=Routine.inputStore 94 (Sort.sortInput records)
    let expected:=Routine.outputStore 94 (Sort.sortOutput records)
    match TestLazy.finishWithin program 3000000 0 (TestLazy.empty program) ⟨0,source⟩ with
    | none=>throw (IO.userError "Complete DAG record sort exceeded fuel")
    | some (steps,last)=>
      unless (List.finRange 96).all (fun r=>last.store r==expected r) do
        throw (IO.userError "Complete DAG record sort full-store mismatch")
      maximum:=max maximum steps
  let program:=commitSignature.program
  let commits : List (Executable.CanonicalState×Sort.Record):=
    [((#[],#[0,0]),(0,zero)),((#[zero],#[9,8]),(0,zero)),((#[zero],#[0,0]),(1,leader)),
      ((#[zero,leader],#[0,1,0]),(2,child))]
  for (state,record) in commits do
    let source : Fin 96→List Bool:=fun r=>
      if r=0 then Encoding.node.encode record.2
      else if r=1 then (Encoding.array Encoding.natural).encode state.2
      else if r=64 then (Encoding.array Encoding.node).encode state.1
      else if r=75 then List.replicate (record.1+1) true
      else if (2≤r.val && r.val≤37) || r=68 then []
      else [false,true]++r.val.bits
    let result:=commitRecord state record
    let expected:=Function.update (Function.update (Function.update (Function.update source 0 []) 75 [])
      1 ((Encoding.array Encoding.natural).encode result.2))
      64 ((Encoding.array Encoding.node).encode result.1)
    match TestLazy.finishWithin program 3000000 0 (TestLazy.empty program) ⟨0,source⟩ with
    | none=>throw (IO.userError "Canonical DAG commit exceeded fuel")
    | some (steps,last)=>
      unless (List.finRange 96).all (fun r=>last.store r==expected r) do
        throw (IO.userError "Canonical DAG commit full-store mismatch")
      maximum:=max maximum steps
  IO.println s!"Canonical DAG components: {cases.length} complete-sort and {commits.length} commit cases passed; maximum {maximum} instructions."

#eval tests
end Counting.StackMachine.DagUpdate.Canonical.Tests
