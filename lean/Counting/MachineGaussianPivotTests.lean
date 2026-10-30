import Counting.MachineGaussianPivot
import Counting.StackMachineTestMemo
import Counting.MachineTestMemo

namespace Counting.Machine.GaussianPivotTests
open DirectedCounting.VerifiedGaussianAnchorSolver RationalSystem StackMachine.GaussianPivot

def system (q : Nat) (rows : List (List Rat)) : RationalSystem q where
  coeff row column := ((rows[row.val]?).getD [])[column.val]?.getD 0
  rhs _ := 0

private def requireStack (program : StackMachine.Program) {q : Nat} (S : RationalSystem q) (pivot : Fin q) : IO Unit := do
  let matrix := Encoding.rationalMatrix.encode (StoredGaussian.augmentedMatrix S)
  let input := inputWord (StoredGaussian.augmentedMatrix S) pivot.val
  let result := (findPivot? S pivot).map Fin.val
  match StackMachine.TestRun.finishWithin program 1000000 (StackMachine.initial program input) with
  | none => throw (IO.userError "Pivot stack search exhausted fuel")
  | some (steps,output) =>
      let expected := Encoding.optionalNatural.encode result
      let correct := (List.finRange (program.extraRegisters+2)).all (fun r => output.store r ==
        (if r.val=0 then matrix else if r.val=1 then expected else if r.val=2 then List.replicate (pivot.val+1) true
         else if r.val=30 then [result.isNone] else []))
      unless correct do throw (IO.userError s!"Incorrect pivot full-store result at {pivot.val}: expected {result}")
      IO.println s!"Pivot {pivot.val} -> {result}: {steps} stack transitions, full store checked."

private def requirePhysical (program : Program) : IO Unit := do
  let S := system 1 [[0]]
  let input := inputWord (StoredGaussian.augmentedMatrix S) 0
  let expected := Encoding.optionalNatural.encode none
  match TestMemo.finishWithin program 3000000 0 (TestMemo.empty program) (initial program input) with
  | none => throw (IO.userError "Physical pivot exhausted fuel")
  | some (steps,output) =>
      let right := output.tape.head::output.tape.right
      let clean := output.tape.left.all (· == .blank) && right.take expected.length == expected.map bitSymbol &&
        (right.drop expected.length).all (· == .blank)
      unless clean do throw (IO.userError "Physical pivot output incorrect or tape not clean")
      IO.println s!"Physical absent pivot: {steps} transitions, complete clean tape checked."

def tests : IO Unit := do
  let stack := StackMachine.TestRun.tabulate complete.program
  requireStack stack (system 1 [[0]]) 0
  requireStack stack (system 1 [[-1/3]]) 0
  requireStack stack (system 3 [[0,0,1],[2,0,0],[3,0,4]]) 0
  requireStack stack (system 3 [[0,0,1],[2,0,0],[3,0,4]]) 1
  requireStack stack (system 3 [[0,0,1],[2,0,0],[3,0,4]]) 2
  requireStack stack (system 3 [[9,0,0],[0,0,0],[0,1/2,0]]) 1
  let physical := gaussianPivotProgram
  requirePhysical physical
  IO.println "6 full-store pivot cases and 1 physical clean-tape case passed."

#eval tests

end Counting.Machine.GaussianPivotTests
