import Counting.ExternalSATMachine
import Counting.StackMachineTestMemo

namespace Counting.External.SATVerification.MemoTests
open StackMachine

private def checked (program : Program) (input : List Bool) : IO Unit := do
  match TestRun.finishWithin program 500000 (initial program input) with
  | none => throw (IO.userError "SAT verifier exceeded test fuel")
  | some (_time,finish) =>
    unless finish.store 1==[verify input] do
      throw (IO.userError "SAT verifier disagrees with mathematical checker")

def tests : IO Unit := do
  let program := TestRun.tabulate stackVerifier
  for input in [[],[true],[true,false],[true,true]] do checked program input
  let instances : List (CNFEncoding.Raw × List Bool) :=
    [(([],[]),[]),(([],[[]]),[]),(([true],[[(0,true)]]),[true]),
     (([true],[[(0,true)]]),[false]),(([true],[[(0,false)]]),[false]),
     (([true],[[(0,true)],[(0,false)]]),[true]),(([false],[]),[true]),
     (([true],[[(1,true)]]),[true]),(([true],[]),[]),
     (([true],[[(2^128,false)]]),[false])]
  for pair in instances do
    checked program (Encoding.pairWords (CNFEncoding.rawCodec.encode pair.1) pair.2)
  IO.println "SAT verifier passed 14 concrete stack executions (with the proved-identical finite instruction table and register stores), including malformed input, empty clauses, invalid markers, wrong witness lengths and a 128-bit index."

#eval tests
end Counting.External.SATVerification.MemoTests
