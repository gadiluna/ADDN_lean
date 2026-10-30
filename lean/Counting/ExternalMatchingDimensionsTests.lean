import Counting.ExternalMatchingDimensions
import Counting.StackMachineTestMemo

namespace Counting.External.MatchingDimensions.Tests
open StackMachine

private def workspace : Workspace 2 := ⟨![2,0,1,3,4,5,6,7,8,9,10,11],by decide⟩

private def checked (program : Program) (registers : program.extraRegisters+2=14)
    (n m : Nat) : IO Unit := do
  let store : Fin 14 → List Bool := fun r =>
    if r=2 then List.replicate n true else if r=0 then List.replicate m true
    else if r=12 then [true,false] else if r=13 then [false,true,true] else []
  let expected := result workspace n m store
  let castStore : Fin (program.extraRegisters+2) → List Bool := fun r => store (r.cast registers)
  match TestRun.finishWithin program (cost n m+1) ⟨0,castStore⟩ with
  | none => throw (IO.userError "matching dimension counters exceeded the exact proved cost")
  | some (steps,finish) =>
    unless steps==cost n m && (List.finRange (program.extraRegisters+2)).all
        (fun r => finish.store r==expected (r.cast registers)) do
      throw (IO.userError "matching dimensions changed input, scratch, outside state or an output counter")

def tests : IO Unit := do
  let program := TestRun.tabulate (routine 2 workspace).program
  for n in List.range 3 do
    for m in List.range 3 do checked program rfl n m
  checked program rfl 4 1
  checked program rfl 1 5
  IO.println "Matching dimensions: 11 full-store executions passed, including zero counters, truncated subtraction and nonempty external registers; exact step counts agree."

#eval tests
end Counting.External.MatchingDimensions.Tests
