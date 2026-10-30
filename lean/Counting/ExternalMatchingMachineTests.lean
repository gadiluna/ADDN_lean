import Counting.ExternalMatchingMachine
import Counting.StackMachineTestLazy

namespace Counting.External.MatchingMachine.Tests
open StackMachine

private def checked (program : Program) (input : List Bool) : IO Unit := do
  match TestLazy.finishWithin program 2000000 0 (TestLazy.empty program) (initial program input) with
  | none => throw (IO.userError "three-SAT-to-matching generator exceeded concrete test fuel")
  | some (time,finish) =>
    unless finish.store 1==reduceMatching input do
      throw (IO.userError "three-SAT-to-matching generator output mismatch")
    IO.println s!"checked three-SAT-to-matching: {input.length} input bits, {time} stack transitions"

def tests : IO Unit := do
  let program := stackGenerator
  for input in [[],[true],[true,false]] do checked program input
  let instances : List CNFEncoding.Raw := [
    ([],[]),([],[[]]),([true],[]),([true],[[(0,true),(0,true),(0,true)]]),
    ([true],[[(0,false),(0,true),(0,false)]]),
    ([true],[[(0,true),(0,true),(0,true)],[(0,false),(0,false),(0,false)]]),
    ([true,true],[[(0,false),(1,true),(0,true)]]),
    ([true],[[(0,true)]]),([false],[]),([true],[[(1,true),(0,true),(0,true)]]),
    ([true],[[(2^128,false),(0,true),(0,true)]])]
  for raw in instances do checked program (CNFEncoding.rawCodec.encode raw)
  IO.println "Three-SAT-to-matching: 14 total actual executions passed, including empty instances, both signs, negative formulas, wrong clause size, invalid universe/ranges and a 128-bit malformed index."
#eval tests
end Counting.External.MatchingMachine.Tests
