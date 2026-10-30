import Counting.MachineDagImport
import Counting.StackMachineTestLazy
import Counting.MachineTestMemo

namespace Counting.Machine.DagImportTests
open StackMachine.DagUpdate.Import

def stackTests : IO Unit := do
  let program := completeImport.program
  let root : Executable.Node := ⟨0,none,false,0,[]⟩
  let leader : Executable.Node := ⟨0,none,true,0,[]⟩
  let child : Executable.Node := ⟨1,some 0,false,2,[(0,2)]⟩
  let cases : List (Array Executable.Node×List Executable.Node) :=
    [(#[],[]),(#[root],[]),(#[],[root]),(#[root],[root]),(#[leader],[root,child])]
  let mut maximum := 0
  for (pool,nodes) in cases do
    let input := importInput pool nodes
    let expected := StackMachine.Routine.outputStore 94 (importOutput pool nodes)
    match StackMachine.TestLazy.finishWithin program 20000000 0 (StackMachine.TestLazy.empty program)
        ⟨0,StackMachine.Routine.inputStore 94 input⟩ with
    | none => throw (IO.userError "Closed DAG importer exceeded stack fuel")
    | some (steps,finish) =>
      unless (List.finRange 96).all (fun r=>finish.store r==expected r) do
        throw (IO.userError "Closed DAG importer full-store mismatch")
      maximum := max maximum steps
  IO.println s!"Closed DAG importer: {cases.length} full-store cases passed; maximum {maximum} instructions."

def physicalTests : IO Unit := do
  let program := dagImportProgram
  let root : Executable.Node := ⟨0,none,false,0,[]⟩
  let cases : List (Array Executable.Node×List Executable.Node) := [(#[],[]),(#[],[root])]
  for (pool,nodes) in cases do
    let word := importInput pool nodes
    let expected := importOutput pool nodes
    match TestMemo.finishWithin program 100000000 0 (TestMemo.empty program) (initial program word) with
    | none => throw (IO.userError "Physical DAG importer exceeded fuel")
    | some (steps,finish) =>
      let right := finish.tape.head::finish.tape.right
      unless finish.tape.left.all (· == .blank) &&
          right.take expected.length==expected.map bitSymbol &&
          (right.drop expected.length).all (· == .blank) do
        throw (IO.userError "Physical DAG importer has wrong output or dirty work tape")
      IO.println s!"DAG importer physical run: {steps} transitions, exact clean output."

#eval stackTests
#eval physicalTests
end Counting.Machine.DagImportTests
