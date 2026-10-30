import Counting.StackRealizabilityMachineSpec
import Counting.StackMachineTestLazy

namespace Counting.StackMachine.RealizabilityCheck.TotalTests

private def requireRun (name : String) (input : List Bool) (expected : Bool) : IO Nat := do
  unless encodedVerifier input==expected do
    throw (IO.userError s!"Realizability specification disagrees with the known case: {name}")
  let program := totalVerifier.program
  match TestLazy.finishWithin program 4000000 0 (TestLazy.empty program) (initial program input) with
  | none => throw (IO.userError s!"Total realizability verifier exhausted fuel: {name}")
  | some (time,result) =>
    unless result.store 1==[expected] do
      throw (IO.userError s!"Total realizability verifier returned a different Boolean: {name}")
    return time

/-- Focused end-to-end regressions for the new composition. Existing
round and component suites exercise their detailed full-store contracts. -/
def tests : IO Unit := do
  let root : Executable.Node := ⟨0,none,true,0,[]⟩
  let next : Executable.Node := ⟨1,some 0,true,0,[]⟩
  let initialVista : Executable.Vista := ⟨#[root],0⟩
  let finalVista : Executable.Vista := ⟨#[root,next],1⟩
  let good := Encoding.verifierInput.encode (finalVista,[1,1],1,1)
  let cases := [
    ("empty binary input",[],false),
    ("invalid semantic DAG",Encoding.verifierInput.encode ((⟨#[],0⟩:Executable.Vista),[],1,1),false),
    ("depth-zero realizability",Encoding.verifierInput.encode (initialVista,[1],1,1),true),
    ("singleton zero-arc round",good,true),
    ("zero count rejected",Encoding.verifierInput.encode (finalVista,[0,1],1,1),false),
    ("wrong count dimension",Encoding.verifierInput.encode (finalVista,[1],1,1),false),
    ("trailing binary suffix",good++[true],false)]
  let mut maximum := 0
  for (name,input,expected) in cases do
    let time ← requireRun name input expected
    maximum := max maximum time
  IO.println s!"Total realizability verifier passed {cases.length} end-to-end cases; maximum {maximum} instructions."

#eval tests
end Counting.StackMachine.RealizabilityCheck.TotalTests
