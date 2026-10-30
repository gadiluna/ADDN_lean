import Counting.StackDagCanonicalInitialize
import Counting.StackMachineTestLazy

namespace Counting.StackMachine.DagUpdate.Canonical.InitializeTests
open Routine RealizabilityCall

def tests : IO Unit := do
  let leader := Executable.initialVista true
  let follower := Executable.initialVista false
  let child : Executable.Vista :=
    ⟨#[⟨0,none,false,0,[]⟩,⟨1,some 0,false,2^65+1,[(0,2^65+1)]⟩],1⟩
  let cases : List (String×Executable.Vista) :=
    [("empty malformed DAG",⟨#[],17⟩),("leader",leader),("follower",follower),
     ("large multiplicity",child),("invalid huge bottom",⟨leader.nodes,2^80+1⟩)]
  let program := initializeCanonical.program
  for (name,source) in cases do
    let input := Encoding.vista.encode source
    let expected := file (initializeData source)
    match TestLazy.finishWithin program 5000000 0 (TestLazy.empty program) ⟨0,inputStore 128 input⟩ with
    | none => throw (IO.userError s!"Canonical initialization exhausted fuel: {name}")
    | some (steps,last) =>
      unless (List.finRange 130).all (fun r=>last.store r==expected r) do
        throw (IO.userError s!"Canonical initialization full-store mismatch: {name}")
      unless steps ≤ initializeCoefficient*(input.length+1)^4 do
        throw (IO.userError s!"Canonical initialization exceeded proved bound: {name}")
      IO.println s!"Canonical initialization {name}: {steps} instructions; all 130 registers checked."
  IO.println "Five canonical initialization regressions passed."

#eval tests
end Counting.StackMachine.DagUpdate.Canonical.InitializeTests
