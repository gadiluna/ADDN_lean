import Counting.MachineGaussianLinear
import Counting.StackMachineTestLazy

namespace Counting.Machine.GaussianLinearSmallTests

private def requireOutput (program : StackMachine.Program) (input expected : List Bool)
    (name : String) (fuel : Nat) : IO Unit := do
  match StackMachine.TestLazy.finishWithin program fuel 0 (StackMachine.TestLazy.empty program)
      (StackMachine.initial program input) with
  | none => throw (IO.userError s!"Gaussian small regression exhausted fuel: {name}")
  | some (steps,output) =>
    let exact := (List.finRange (program.extraRegisters+2)).all
      (fun r=>output.store r == if r.val=1 then expected else [])
    unless exact do throw (IO.userError s!"Gaussian small regression differs: {name}")
    IO.println s!"{name}: {steps} stack transitions; all registers checked."

/-- Deliberately bounded replacement regressions. The larger Gaussian,
dot, row-operations and Axpy suites were interrupted with exit 130 after
long runtimes; no result from those interrupted suites is counted here. -/
def tests : IO Unit := do
  let appendProgram := StackMachine.GaussianAugmentVector.routine.program
  for values in ([[],[0],[1],[-1],[1/2,-3/4],[0,0,0]] : List (List Rat)) do
    requireOutput appendProgram (Encoding.rationalRow.encode values)
      (Encoding.rationalRow.encode (values++[-1])) s!"Append -1 to {values}" 10000
  let input := StackMachine.GaussianNormal.inputWord 0 []
  let expected := (Encoding.optional Encoding.rationalRow).encode (some [])
  requireOutput StackMachine.GaussianCalls.complete.program input expected "Rectangular solver width0/rows0" 20000
  IO.println "6 append-vector cases and 1 complete empty rectangular-solver case passed."

#eval tests

end Counting.Machine.GaussianLinearSmallTests
