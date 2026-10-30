import Counting.StackDagCanonicalOneLevel
import Counting.StackMachineTestLazy

namespace Counting.StackMachine.DagUpdate.Canonical.LevelTests
open Routine RealizabilityCall

def tests : IO Unit := do
  let plain : Executable.Node := ⟨0,none,false,0,[]⟩
  let leader : Executable.Node := ⟨0,none,true,0,[]⟩
  let child : Executable.Node := ⟨1,some 0,false,2^40+3,[(0,2^40+3)]⟩
  let cases : List (String×Executable.Vista×Executable.CanonicalState×Nat) :=
    [("empty level",⟨#[plain],0⟩,(#[],#[0]),1),
     ("leader root",⟨#[leader],0⟩,(#[],#[0]),0),
     ("sorted roots",⟨#[leader,plain],1⟩,(#[],#[0,0]),0),
     ("reindexed child",⟨#[plain,child],1⟩,(#[plain],#[0,0]),1)]
  let program := oneLevel.program
  for (name,source,state,level) in cases do
    let data : Fin 30 → List Bool := fun r=>
      if r=1 then (Encoding.array Encoding.natural).encode state.2
      else if r=2 then (Encoding.array Encoding.node).encode state.1
      else if r=20 then (Encoding.array Encoding.node).encode source.nodes
      else if r=22 then level.bits
      else if 26≤r.val then []
      else [true,false]++r.val.bits
    let expected := file (oneLevelData data (Executable.canonicalLevel source state level) level)
    match TestLazy.finishWithin program 10000000 0 (TestLazy.empty program) ⟨0,file data⟩ with
    | none => throw (IO.userError s!"Canonical level exhausted fuel: {name}")
    | some (steps,last) =>
      unless (List.finRange 130).all (fun r=>last.store r==expected r) do
        throw (IO.userError s!"Canonical level output/preserved register mismatch: {name}")
      IO.println s!"Canonical level {name}: {steps} instructions; all 130 registers checked."
  IO.println "Four complete canonical level regressions passed."

#eval tests
end Counting.StackMachine.DagUpdate.Canonical.LevelTests

