import Counting.MachineRowScaleGaussian
import Counting.MachineTestMemo
import Counting.StackMachineTestMemo

namespace Counting.Machine.RowScaleTests
open StackMachine.RowScale

private def requireRow (program : Program) (factor : Rat) (row : List Rat) : IO Unit := do
  let input := inputCodec.encode (factor,row)
  let expected := Encoding.rationalRow.encode (row.map (factor*·))
  match TestMemo.finishWithin program 15000000 0 (TestMemo.empty program) (initial program input) with
  | none => throw (IO.userError s!"Row scaling exhausted fuel: {factor} * {row}")
  | some (steps,result) =>
      let right := result.tape.head::result.tape.right
      let clean := result.tape.left.all (· == .blank) &&
        right.take expected.length == expected.map bitSymbol &&
        (right.drop expected.length).all (· == .blank)
      unless clean do throw (IO.userError s!"Row scaling incorrect or dirty tape: {factor} * {row}")
      IO.println s!"Row scaling {factor} * {row}: {steps} transitions, clean output."

private def requireStackRow (program : StackMachine.Program) (factor : Rat) (row : List Rat) : IO Unit := do
  let input := inputCodec.encode (factor,row)
  let expected := Encoding.rationalRow.encode (row.map (factor*·))
  match StackMachine.TestRun.finishWithin program 1000000 (StackMachine.initial program input) with
  | none => throw (IO.userError s!"Stack row scaling exhausted fuel: {factor} * {row}")
  | some (steps,result) =>
      let correct := (List.finRange (program.extraRegisters+2)).all (fun r =>
        result.store r == (if r.val=0 then Encoding.rational.encode factor else if r.val=1 then expected else []))
      unless correct do throw (IO.userError s!"Stack row scaling incorrect full store: {factor} * {row}")
      IO.println s!"Stack row scaling {factor} * {row}: {steps} transitions, full store checked."

/-- The earlier physical-only suite was interrupted because its host interpreter
was too slow. These cases retain the same real stack program, materializing its
finite code and store; the empty case additionally runs the physical tape. -/
def tests : IO Unit := do
  let stack := StackMachine.TestRun.tabulate complete.program
  for (factor,row) in ([(3,[]),(0,[1,-2]),(2,[1/2,-1/3]),(-1,[0,3/4]),(1/2,[3])] : List (Rat×List Rat)) do
    requireStackRow stack factor row
  let physical := rowScaleProgram
  requireRow physical 3 []
  IO.println "5 full-store row-scaling cases and 1 physical clean-tape case passed."

#eval tests

end Counting.Machine.RowScaleTests
