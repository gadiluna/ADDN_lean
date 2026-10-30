import Counting.ExternalCoverMachine
import Counting.StackMachineTestLazy

namespace Counting.External.CoverMachine.Tests
open StackMachine

private def checked (program : Program) (input : List Bool) : IO Unit := do
  match TestLazy.finishWithin program 2000000 0 (TestLazy.empty program) (initial program input) with
  | none => throw (IO.userError "matching-to-cover generator exceeded concrete test fuel")
  | some (time,finish) =>
    unless finish.store 1==reduceCover input do
      throw (IO.userError "matching-to-cover generator output mismatch")
    IO.println s!"checked matching-to-cover: {input.length} input bits, {time} stack transitions"

def tests : IO Unit := do
  let program := stackGenerator
  for input in [[],[true],[true,false]] do checked program input
  let instances : List ThreeDMEncoding.Raw := [
    ([],[]),([],[[]]),([true],[]),([true],[[0,0,0]]),
    ([true,true],[[0,1,0],[1,0,1]]),([true,true],[[0,0,0],[0,0,0]]),
    ([true,true,true],[[2,0,1]]),([true],[[0]]),([false],[]),
    ([true],[[1,0,0]]),([true],[[2^128,0,0]])]
  for raw in instances do checked program (ThreeDMEncoding.rawCodec.encode raw)
  IO.println "Matching-to-cover: 14 total actual executions passed, including empty instances, repeated triples, wrong triple size, invalid universe/ranges and a 128-bit malformed index."
#eval tests
end Counting.External.CoverMachine.Tests
