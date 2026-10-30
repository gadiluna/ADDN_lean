import Counting.ExternalThreeSATVerifierMachine
import Counting.StackMachineTestMemo

namespace Counting.External.ThreeSATVerification.Tests
open StackMachine

private def checked (program : Program) (input : List Bool) (expected : Bool) : IO Unit := do
  unless verify input==expected do
    throw (IO.userError "three-SAT reference result differs from the specified test expectation")
  match TestRun.finishWithin program 1500000 (initial program input) with
  | none => throw (IO.userError "three-SAT verifier exceeded concrete test fuel")
  | some (time,finish) =>
    unless finish.store 1==[expected] do
      throw (IO.userError "three-SAT verifier differs from the specified test expectation")
    IO.println s!"three-SAT verifier: {input.length} input bits, {time} stack transitions, {expected}"

def tests : IO Unit := do
  let program := TestRun.tabulate stackVerifier
  for input in [[],[true],[true,false],[true,true]] do checked program input false
  let positive := (0,true)
  let negative := (0,false)
  let triple := [positive,positive,positive]
  let instances : List (CNFEncoding.Raw × List Bool × Bool) :=
    [(([],[]),[],true),(([],[[]]),[],false),
     (([true],[triple]),[true],true),(([true],[triple]),[false],false),
     (([true],[[negative,negative,negative]]),[false],true),
     (([true],[[positive,negative,positive]]),[false],true),
     (([true],[[positive]]),[true],false),
     (([true],[[positive,positive]]),[true],false),
     (([true],[[positive,positive,positive,positive]]),[true],false),
     (([true],[triple,[positive]]),[true],false),
     (([true],[triple,[negative,negative,negative]]),[true],false),
     (([true],[triple]),[],false),(([true],[triple]),[true,false],false),
     (([false],[triple]),[true],false),
     (([true],[[(1,true),positive,positive]]),[true],false),
     (([true],[[(2^128,false),positive,positive]]),[true],false)]
  for pair in instances do
    checked program (Encoding.pairWords (CNFEncoding.rawCodec.encode pair.1) pair.2.1) pair.2.2
  IO.println "Three-SAT verifier: 20 actual executions passed; exact clause width, both signs, malformed inputs, invalid indices/markers and witness lengths."

#eval tests
end Counting.External.ThreeSATVerification.Tests
