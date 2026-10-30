import Counting.MachineMatrixAxpyGaussian
import Counting.StackMachineTestMemo
import Counting.MachineTestMemo

namespace Counting.Machine.MatrixAxpyTests
open StackMachine.MatrixAxpy

private def requireStack (program : StackMachine.Program) (factor : Rat) (rows : List (List Rat))
    (target source : Nat) : IO Unit := do
  let input := inputWord factor rows target source
  let replacement := List.zipWith (fun a b=>a+factor*b) (rows[target]?.getD []) (rows[source]?.getD [])
  let expected := Encoding.rationalMatrix.encode (rows.set target replacement)
  match StackMachine.TestRun.finishWithin program 1000000 (StackMachine.initial program input) with
  | none => throw (IO.userError "Matrix Gaussian addition exhausted stack fuel")
  | some (steps,output) =>
      let correct := (List.finRange (program.extraRegisters+2)).all (fun r => output.store r ==
        (if r.val=0 then Encoding.rational.encode factor else if r.val=1 then expected else []))
      unless correct do throw (IO.userError s!"Incorrect full store for matrix addition {target}+={factor}*{source}")
      IO.println s!"Matrix addition {target}+={factor}*{source}: {steps} stack transitions, full store checked."

private def requirePhysical (program : Program) : IO Unit := do
  let input := inputWord (-1) [[]] 0 0
  let expected := Encoding.rationalMatrix.encode [[]]
  match TestMemo.finishWithin program 5000000 0 (TestMemo.empty program) (initial program input) with
  | none => throw (IO.userError "Physical matrix Gaussian addition exhausted fuel")
  | some (steps,output) =>
      let right := output.tape.head::output.tape.right
      let clean := output.tape.left.all (· == .blank) && right.take expected.length == expected.map bitSymbol &&
        (right.drop expected.length).all (· == .blank)
      unless clean do throw (IO.userError "Physical matrix Gaussian addition returned incorrect or dirty tape")
      IO.println s!"Physical equal-index empty row: {steps} transitions, complete clean tape checked."

def tests : IO Unit := do
  let stack := StackMachine.TestRun.tabulate complete.program
  requireStack stack 2 [[]] 0 0
  requireStack stack (-1) [[1]] 0 0
  requireStack stack 2 [[1/2,3],[2,-1]] 0 1
  requireStack stack 0 [[1/2,3],[2,-1]] 0 1
  requireStack stack (-1) [[1/2,3],[2,-1]] 1 0
  requireStack stack (1/2) [[1],[2],[3]] 2 0
  requireStack stack 3 [[1],[2],[3]] 0 2
  let physical := matrixAxpyProgram
  requirePhysical physical
  IO.println "7 full-store matrix addition cases and 1 physical clean-tape case passed."

#eval tests

end Counting.Machine.MatrixAxpyTests
