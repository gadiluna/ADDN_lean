import Counting.MachineRowAxpyGaussian
import Counting.MachineRowAdd
import Counting.MachineTestMemo
import Counting.StackMachineTestMemo

namespace Counting.Machine.RowOperationsTests

private def requireRun (program : Program) (name : String) (input expected : List Bool) : IO Unit := do
  match TestMemo.finishWithin program 30000000 0 (TestMemo.empty program) (initial program input) with
  | none => throw (IO.userError s!"Row operation exhausted fuel: {name}")
  | some (steps,result) =>
      let right := result.tape.head::result.tape.right
      let clean := result.tape.left.all (· == .blank) &&
        right.take expected.length == expected.map bitSymbol &&
        (right.drop expected.length).all (· == .blank)
      unless clean do throw (IO.userError s!"Row operation incorrect or dirty tape: {name}")
      IO.println s!"Row operation {name}: {steps} transitions, clean output."

private def requireStack (program : StackMachine.Program) (name : String) (input factor expected : List Bool) : IO Unit := do
  match StackMachine.TestRun.finishWithin program 2000000 (StackMachine.initial program input) with
  | none => throw (IO.userError s!"Stack row operation exhausted fuel: {name}")
  | some (steps,result) =>
      let correct := (List.finRange (program.extraRegisters+2)).all (fun r =>
        result.store r == (if r.val=0 then factor else if r.val=1 then expected else []))
      unless correct do throw (IO.userError s!"Stack row operation incorrect full store: {name}")
      IO.println s!"Stack row operation {name}: {steps} transitions, full store checked."

/-- The earlier six-case physical suite was interrupted for host-interpreter
cost. All six cases check the entire actual stack state; the empty cases also
execute the compiled physical machines and check the complete clean tape. -/
def tests : IO Unit := do
  let addStack := StackMachine.TestRun.tabulate StackMachine.RowAdd.complete.program
  for (left,right) in ([([],[]),([1/2,-1],[1/3,1]),([-2],[3])] : List (List Rat×List Rat)) do
    requireStack addStack s!"{left}+{right}" (StackMachine.RowAdd.inputCodec.encode (left,right)) []
      (Encoding.rationalRow.encode (List.zipWith (·+·) left right))
  let axpyStack := StackMachine.TestRun.tabulate StackMachine.RowAxpy.complete.program
  for (factor,(target,source)) in ([(2,([],[])),(2,([1,-1],[1/2,1/3])),(-1,([3/4],[3/4]))] : List (Rat×(List Rat×List Rat))) do
    requireStack axpyStack s!"{target}+{factor}*{source}"
      (StackMachine.RowAxpy.inputCodec.encode (factor,(target,source))) (Encoding.rational.encode factor)
      (Encoding.rationalRow.encode (List.zipWith (fun a b => a+factor*b) target source))
  let add := rowAddProgram
  requireRun add "empty addition" (StackMachine.RowAdd.inputCodec.encode ([],[])) (Encoding.rationalRow.encode [])
  let axpy := rowAxpyProgram
  requireRun axpy "empty Gaussian addition" (StackMachine.RowAxpy.inputCodec.encode (2,([],[]))) (Encoding.rationalRow.encode [])
  IO.println "6 full-store row-operation cases and 2 physical clean-tape cases passed."

#eval tests

end Counting.Machine.RowOperationsTests
