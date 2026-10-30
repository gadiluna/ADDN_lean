import Counting.ExternalSATMachine

namespace Counting.External.SATVerification.Tests
open StackMachine

private def finishWithin : Nat → Config stackVerifier → Option (Config stackVerifier)
  | 0,_ => none
  | fuel+1,config => match step stackVerifier config with
    | none => some config
    | some next => finishWithin fuel next

private def checked (input : List Bool) : IO Unit := do
  match finishWithin 500000 (initial stackVerifier input) with
  | none => throw (IO.userError "SAT verifier exceeded test fuel")
  | some finish =>
    unless finish.store 1==[verify input] do
      throw (IO.userError "SAT verifier disagrees with mathematical checker")

def tests : IO Unit := do
  for input in [[],[true],[true,false],[true,true]] do checked input
  let instances : List (CNFEncoding.Raw × List Bool) :=
    [(([],[]),[]),(([],[[]]),[]),(([true],[[(0,true)]]),[true]),
     (([true],[[(0,true)]]),[false]),(([true],[[(0,false)]]),[false]),
     (([true],[[(0,true)],[(0,false)]]),[true]),(([false],[]),[true]),
     (([true],[[(1,true)]]),[true]),(([true],[]),[]),
     (([true],[[(2^128,false)]]),[false])]
  for pair in instances do
    checked (Encoding.pairWords (CNFEncoding.rawCodec.encode pair.1) pair.2)
  IO.println "SAT verifier passed 14 concrete stack executions, including malformed input, empty clauses, invalid markers, wrong witness lengths and a 128-bit index."

#eval tests
end Counting.External.SATVerification.Tests
