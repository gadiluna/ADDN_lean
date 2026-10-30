import Counting.ExternalCoverVerifierMachine
import Counting.StackMachineTestLazy

namespace Counting.External.CoverVerification.Tests
open StackMachine
private def checked (program : Program) (word : List Bool) : IO Nat := do
  match TestLazy.finishWithin program 4000000 0 (TestLazy.empty program) (initial program word) with
  | none => throw (IO.userError "X3C total verifier exceeded concrete test fuel")
  | some (steps,finish) =>
    unless finish.store 1==[verify word] do
      throw (IO.userError "X3C total verifier output mismatch")
    IO.println s!"X3C verifier: {word.length} input bits, {steps} stack transitions."
    return steps

def tests : IO Unit := do
  let program := stackVerifier
  let mut maximum := 0
  for word in [[],[true],[true,false],[false]] do
    maximum := max maximum (←checked program word)
  let cases : List (X3CEncoding.Raw×List Bool) := [
    (([],[]),[]),(([],[]),[false]),((List.replicate 3 true,[]),[]),
    ((List.replicate 3 true,[[0,1,2]]),[true]),((List.replicate 3 true,[[0,1,2]]),[false]),
    ((List.replicate 3 true,[[0,1,2]]),[]),((List.replicate 3 true,[[0,1,2]]),[true,true]),
    ((List.replicate 3 true,[[0,1,2],[0,1,2]]),[true,false]),
    ((List.replicate 3 true,[[0,1,2],[0,1,2]]),[true,true]),
    ((List.replicate 6 true,[[0,1,2],[3,4,5]]),[true,true]),
    ((List.replicate 6 true,[[0,1,2],[2,3,4]]),[true,true]),
    (([true,true],[]),[]),(([true,false,true],[]),[]),
    ((List.replicate 3 true,[[0,0,2]]),[true]),((List.replicate 3 true,[[2,1,0]]),[true]),
    ((List.replicate 3 true,[[0,1,3]]),[true]),((List.replicate 3 true,[[0,1,2^128]]),[true])]
  for (raw,mask) in cases do
    maximum := max maximum (←checked program (Encoding.pairWords (X3CEncoding.rawCodec.encode raw) mask))
  IO.println s!"X3C total verifier: 21 actual stack output cases passed, including malformed framing, bad mask length, repeated rows and a 129-bit index; maximum {maximum} transitions."
#eval tests
end Counting.External.CoverVerification.Tests
