import Counting.MachineGaussianInputBounds
import Counting.StackMachineTestLazy
import Counting.MachineTestMemo

namespace Counting.Machine.GaussianTests
open DirectedCounting.VerifiedGaussianAnchorSolver

private def fromRows (rows : List (List Rat)) : RationalSystem rows.length where
  coeff row column := ((rows[row.val]?.getD [])[column.val]?).getD 0
  rhs row := ((rows[row.val]?.getD [])[rows.length]?).getD 0

private def requireStack (program : StackMachine.Program) (name : String) (rows : List (List Rat)) : IO Unit := do
  let system := fromRows rows
  let input := Encoding.rationalMatrix.encode (StoredGaussian.augmentedMatrix system)
  let expected := StackMachine.GaussianBank.outputStore (StoredGaussian.runGaussian system)
  match StackMachine.TestLazy.finishWithin program 2000000 0 (StackMachine.TestLazy.empty program)
      (StackMachine.initial program input) with
  | none => throw (IO.userError s!"Gaussian stack fuel exhausted: {name}")
  | some (steps,result) =>
    unless program.extraRegisters==51 do throw (IO.userError "Gaussian register layout changed")
    let exactStore := (List.finRange 53).all (fun r =>
      if inside : r.val<program.extraRegisters+2 then result.store ⟨r.val,inside⟩ == expected r else false)
    unless exactStore do throw (IO.userError s!"Gaussian result or transcript differs: {name}")
    IO.println s!"Gaussian {name}: {steps} stack transitions, all 53 registers checked."

private def requirePhysical (program : Program) : IO Unit := do
  let input := Encoding.rationalMatrix.encode []
  let expected := (Encoding.optional Encoding.rationalRow).encode (some [])
  match TestMemo.finishWithin program 1000000 0 (TestMemo.empty program) (initial program input) with
  | none => throw (IO.userError "Gaussian empty physical run exhausted fuel")
  | some (steps,result) =>
    let right := result.tape.head::result.tape.right
    let clean := result.tape.left.all (· == .blank) &&
      right.take expected.length == expected.map bitSymbol &&
      (right.drop expected.length).all (· == .blank)
    unless clean do throw (IO.userError "Gaussian empty physical run returned incorrect or dirty tape")
    IO.println s!"Gaussian empty system: {steps} physical transitions, complete clean tape checked."

def tests : IO Unit := do
  let stack := StackMachine.GaussianBank.complete.program
  requireStack stack "dimension zero" []
  requireStack stack "unit pivot" [[1,2]]
  requireStack stack "negative reciprocal" [[-2,3]]
  requireStack stack "singular consistent" [[0,0]]
  requireStack stack "singular inconsistent" [[0,1]]
  requireStack stack "off-diagonal swap" [[0,1,2],[1,0,3]]
  requireStack stack "dependent rows" [[1,1,2],[2,2,4]]
  requirePhysical gaussianProgram
  IO.println "7 full-store Gaussian cases and 1 physical clean-tape case passed."

#eval tests

end Counting.Machine.GaussianTests
