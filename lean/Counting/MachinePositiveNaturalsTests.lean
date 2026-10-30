import Counting.MachinePositiveNaturals
import Counting.MachineTestMemo
import Counting.StackMachineTestMemo

namespace Counting.Machine.PositiveNaturalsTests
open StackMachine

private def stackTest (program : StackMachine.Program) (registers : program.extraRegisters=30)
    (row : List Rat) (suffix : List Bool) : IO Unit := do
  let input := Encoding.rationalRow.encode row
  let result := Counting.PositiveNaturals.output row
  let store : Register program → List Bool := fun r =>
    RowScale.file [] (input++suffix) [] [] [] [] [] [] []
      ⟨r.val,by simpa [registers] using r.isLt⟩
  let expected : Register program → List Bool := fun r =>
    RowScale.file [] suffix result [] [] [] [] [] []
      ⟨r.val,by simpa [registers] using r.isLt⟩
  match StackMachine.TestRun.finishWithin program 5000000 ⟨0,store⟩ with
  | none => throw (IO.userError "Positive natural conversion exhausted stack budget")
  | some (steps,finish) =>
    unless (List.finRange (program.extraRegisters+2)).all (fun r => finish.store r==expected r) &&
        steps≤9000*(input.length+suffix.length+1)^3 do
      throw (IO.userError "Positive natural conversion whole-store or cost failure")
    IO.println s!"Positive natural vector {row}: {steps} stack steps, suffix preserved."

private def physicalTest (program : Machine.Program) (row : List Rat) : IO Unit := do
  let input := Encoding.rationalRow.encode row
  let expected := (Encoding.optional (Encoding.array Encoding.natural)).encode (Executable.positiveNaturals? row.toArray)
  match TestMemo.finishWithin program 50000000 0 (TestMemo.empty program) (Machine.initial program input) with
  | none => throw (IO.userError "Positive natural conversion exhausted physical test budget")
  | some (steps,finish) =>
    let right := finish.tape.head::finish.tape.right
    unless finish.tape.left.all (· == .blank) && right.take expected.length==expected.map bitSymbol &&
        (right.drop expected.length).all (· == .blank) && steps≤(20*10035^2)*(input.length+1)^6 do
      throw (IO.userError "Positive natural conversion wrong optional result, dirty tape or cost failure")
    IO.println s!"Positive natural vector {row}: {steps} physical transitions, clean tape."

def tests : IO Unit := do
  let stackProgram := StackMachine.TestRun.tabulate StackMachine.PositiveNaturals.conversion.program
  let rows : List (List Rat) := [[],[1],[0],[-1],[1/2],[2,3],[2,0,3],[2,-3],[2,3/2],[2^128],[-(2^128)],[2^128,7]]
  for row in rows do
    for suffix in [[],[true,false,true]] do stackTest stackProgram rfl row suffix
  let program := positiveNaturalsProgram
  for row in ([[],[1],[1,2],[1/2]] : List (List Rat)) do physicalTest program row
  IO.println "Positive natural conversion passed 24 full-store and 4 physical cases."

#eval tests
end Counting.Machine.PositiveNaturalsTests
