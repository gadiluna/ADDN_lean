import Counting.MachineGaussianLinear
import Counting.StackMachineTestLazy

namespace Counting.Machine.GaussianLinearOneTests

private def requireOutput (program : StackMachine.Program) (equations : List Executable.Equation)
    (expected : Option (List Rat)) (name : String) : IO Unit := do
  let input := StackMachine.GaussianNormal.inputWord 1 (GaussianNormalMatrix.equationMatrix 1 equations)
  let word := (Encoding.optional Encoding.rationalRow).encode expected
  match StackMachine.TestLazy.finishWithin program 3000000 0 (StackMachine.TestLazy.empty program)
      (StackMachine.initial program input) with
  | none => throw (IO.userError s!"Width-one solver test exhausted fuel: {name}")
  | some (steps,result) =>
    unless (List.finRange (program.extraRegisters+2)).all
        (fun r=>result.store r == if r.val=1 then word else []) do
      throw (IO.userError s!"Width-one solver result or full-store cleanup differs: {name}")
    IO.println s!"{name}: {steps} actual stack transitions; every register checked."

def tests : IO Unit := do
  let program := StackMachine.GaussianCalls.complete.program
  requireOutput program [(#[1],2)] (some [2]) "Width1 unique solution"
  requireOutput program [(#[0],0)] none "Width1 singular consistent"
  requireOutput program [(#[0],1)] none "Width1 inconsistent"
  IO.println "Three width-one rectangular-solver regressions passed."

#eval tests
end Counting.Machine.GaussianLinearOneTests
