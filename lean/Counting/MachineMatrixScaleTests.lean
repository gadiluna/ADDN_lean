import Counting.MachineMatrixScaleGaussian
import Counting.MachineTestMemo
import Counting.StackMachineTestMemo

namespace Counting.Machine.MatrixScaleTests
open StackMachine.MatrixScale

private def stackTest (program : StackMachine.Program) (registers : program.extraRegisters=33)
    (factor : Rat) (rows : List (List Rat)) (index : Fin rows.length) : IO Unit := do
  let matrix := Encoding.rationalMatrix.encode rows
  let scalar := Encoding.rational.encode factor
  let result := Encoding.rationalMatrix.encode (rows.set index.val (rows[index.val].map (factor*·)))
  let source : StackMachine.Register program → List Bool := fun r =>
    file scalar matrix (List.replicate (index.val+1) true) [] [] []
      ⟨r.val,by simpa [registers] using r.isLt⟩
  let expected : StackMachine.Register program → List Bool := fun r =>
    file scalar result [] [] [] [] ⟨r.val,by simpa [registers] using r.isLt⟩
  match StackMachine.TestRun.finishWithin program 3000000 ⟨0,source⟩ with
  | none => throw (IO.userError "Matrix scaling exhausted stack test budget")
  | some (steps,finish) =>
      unless (List.finRange (program.extraRegisters+2)).all (fun r => finish.store r==expected r) &&
          steps≤60000000000*(2*scalar.length+matrix.length+2)^4 do
        throw (IO.userError "Matrix scaling changed an untouched row/scalar, left scratch, or exceeded cost")
      IO.println s!"Matrix scale {factor}, row {index.val}: {steps} stack steps; full store correct."

private def physicalTest : IO Unit := do
  let input := inputWord 0 [[]] 0
  let expected := Encoding.rationalMatrix.encode [[]]
  match TestMemo.finishWithin matrixScaleProgram 10000000 0 (TestMemo.empty matrixScaleProgram)
      (initial matrixScaleProgram input) with
  | none => throw (IO.userError "Matrix scaling exhausted physical test budget")
  | some (steps,finish) =>
      let right := finish.tape.head::finish.tape.right
      unless finish.tape.left.all (· == .blank) && right.take expected.length==expected.map bitSymbol &&
          (right.drop expected.length).all (· == .blank) &&
          steps≤(20*150000000038^2)*(input.length+1)^8 do
        throw (IO.userError "Matrix scaling wrong physical output, dirty tape or cost failure")
      IO.println s!"Matrix scale empty row: {steps} physical transitions; clean output tape."

def tests : IO Unit := do
  let program := StackMachine.TestRun.tabulate scaleRoutine.program
  stackTest program rfl 0 [[]] ⟨0,by decide⟩
  stackTest program rfl (-3) [[],[]] ⟨1,by decide⟩
  stackTest program rfl 0 [[1],[2]] ⟨0,by decide⟩
  stackTest program rfl 1 [[1],[2]] ⟨1,by decide⟩
  stackTest program rfl (-1) [[1],[2]] ⟨0,by decide⟩
  stackTest program rfl (3/2) [[2],[]] ⟨0,by decide⟩
  stackTest program rfl 2 [[1],[],[-1/2,0]] ⟨2,by decide⟩
  physicalTest
  IO.println "Matrix scaling passed seven full-store cases and one physical execution."

#eval tests
end Counting.Machine.MatrixScaleTests
