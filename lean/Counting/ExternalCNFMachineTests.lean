import Counting.ExternalCNFMachine
import Counting.StackMachineTestMemo

namespace Counting.External.CNFMachine.Tests
open StackMachine

private def checked (program : Program) (input : List Bool) : IO Unit := do
  match TestRun.finishWithin program 1000000 (initial program input) with
  | none => throw (IO.userError "SAT-to-three-SAT generator exceeded concrete test fuel")
  | some (time,finish) =>
    unless finish.store 1==reduceThreeSAT input do
      throw (IO.userError "SAT-to-three-SAT generator produced a different canonical formula")
    IO.println s!"checked SAT-to-three-SAT: {input.length} input bits, {time} stack transitions"

def tests : IO Unit := do
  let program := TestRun.tabulate stackGenerator
  for input in [[],[true],[true,false]] do checked program input
  let instances : List CNFEncoding.Raw :=
    [([],[]),([],[[]]),([true],[]),([true],[[(0,true)]]),([true],[[(0,false)]]),
     ([true],[[(0,true)],[(0,false)]]),([true,true],[[(0,true),(1,false)],[]]),
     ([false],[]),([true],[[(1,true)]]),([true],[[(2^128,false)]])]
  for raw in instances do checked program (CNFEncoding.rawCodec.encode raw)
  IO.println "SAT-to-three-SAT: 13 actual executions passed, including zero width, empty formulas and clauses, padding terminals, both signs, invalid markers/ranges and a 128-bit malformed index."

#eval tests
end Counting.External.CNFMachine.Tests
