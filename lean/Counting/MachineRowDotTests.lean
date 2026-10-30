import Counting.MachineRowDot
import Counting.StackMachineTestLazy
import Counting.MachineTestMemo

namespace Counting.Machine.RowDotTests

private def requireStack (program : StackMachine.Program) (name : String) (left right : List Rat) : IO Unit := do
  let input := StackMachine.RowDot.inputCodec.encode (left,right)
  let expected := Encoding.rational.encode ((List.zipWith (·*·) left right).sum)
  match StackMachine.TestLazy.finishWithin program 1000000 0 (StackMachine.TestLazy.empty program)
      (StackMachine.initial program input) with
  | none => throw (IO.userError s!"Dot product stack fuel exhausted: {name}")
  | some (steps,result) =>
    let exactStore := (List.finRange (program.extraRegisters+2)).all
      (fun r => result.store r == if r.val=1 then expected else [])
    unless exactStore do throw (IO.userError s!"Dot product result or scratch differs: {name}")
    IO.println s!"Dot product {name}: {steps} stack transitions, complete register bank checked."

private def requirePhysical (program : Program) : IO Unit := do
  let input := StackMachine.RowDot.inputCodec.encode ([],[])
  let expected := Encoding.rational.encode 0
  match TestMemo.finishWithin program 500000 0 (TestMemo.empty program) (initial program input) with
  | none => throw (IO.userError "Empty dot product physical run exhausted fuel")
  | some (steps,result) =>
    let right := result.tape.head::result.tape.right
    let clean := result.tape.left.all (· == .blank) &&
      right.take expected.length == expected.map bitSymbol &&
      (right.drop expected.length).all (· == .blank)
    unless clean do throw (IO.userError "Empty dot product returned incorrect or dirty tape")
    IO.println s!"Empty dot product: {steps} physical transitions, complete clean tape checked."

def tests : IO Unit := do
  let stack := StackMachine.RowDot.complete.program
  requireStack stack "empty" [] []
  requireStack stack "zero factor" [0] [7]
  requireStack stack "rational signs" [1/2,-1/3] [2,3]
  requireStack stack "mixed denominators" [1/3,1/5] [1/7,1/11]
  requireStack stack "integer cancellation" [2,-3,4] [3,2,0]
  requirePhysical rowDotProgram
  IO.println "5 full-store dot-product cases and 1 physical clean-tape case passed."

#eval tests

end Counting.Machine.RowDotTests
