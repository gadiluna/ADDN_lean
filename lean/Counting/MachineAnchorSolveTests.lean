import Counting.MachineAnchorSolve
import Counting.StackMachineTestLazy

namespace Counting.Machine.AnchorSolveTests

private def check (program : StackMachine.Program) (vista : Executable.Vista)
    (anchor leaders : Nat) (expected : Option (List Rat)) (label : String) : IO Unit := do
  let input := StackMachine.AnchorMatrix.inputWord anchor leaders vista
  let output := (Encoding.optional Encoding.rationalRow).encode expected
  match StackMachine.TestLazy.finishWithin program 4000000 0 (StackMachine.TestLazy.empty program)
      (StackMachine.initial program input) with
  | none => throw (IO.userError s!"Anchor builder/solver exhausted regression fuel: {label}")
  | some (steps,finish) =>
    unless (List.finRange (program.extraRegisters+2)).all (fun r=>finish.store r == if r.val=1 then output else []) do
      throw (IO.userError s!"Anchor builder/solver output or workspace mismatch: {label}")
    IO.println s!"{label}: {steps} actual stack transitions; all 56 registers checked."

def tests : IO Unit := do
  let program := StackMachine.AnchorSolve.routine.program
  let empty : Executable.Vista := ⟨#[],0⟩
  let leader : Executable.Vista := ⟨#[⟨0,none,true,0,[]⟩],0⟩
  let nonleader : Executable.Vista := ⟨#[⟨0,none,false,0,[]⟩],0⟩
  check program empty 0 0 (some []) "Empty DAG, zero-dimensional solution"
  check program leader 0 1 (some [1]) "Anchor zero, one leader"
  check program nonleader 0 0 none "Anchor zero, singular consistent system"
  check program empty 0 1 none "Empty DAG, inconsistent normalization"
  IO.println "Four composed DAG-to-solver regressions passed."

#eval tests
end Counting.Machine.AnchorSolveTests
