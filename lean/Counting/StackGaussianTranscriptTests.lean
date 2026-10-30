import Counting.StackGaussianTranscript
import Counting.StackMachineTestMemo

namespace Counting.StackMachine.GaussianTranscript.Tests

private def workspace : Workspace 2 := ⟨![8,2,4,1,7,0,3,5,9],by decide⟩

private def checked (kind : Kind) (program : Program)
    (registerCount : program.extraRegisters+2=11)
    (first second : Nat) (factor : Rat) (tail counter : List Bool) : IO Unit := do
  let firstBits := List.replicate (first+1) true
  let secondBits := if kind=.scale then [false,false,true] else List.replicate (second+1) true
  let factorBits := if kind=.swap then [false,true] else Encoding.rational.encode factor
  let store : Fin 11 → List Bool := ![[],tail,secondBits,[],factorBits,[],[true,false],counter,firstBits,[],[false,true,true]]
  let encoded := Encoding.rawRowOp.encode (kind.operation first second factor)
  let expected := Function.update (Function.update store 1 (Encoding.frame encoded++tail)) 7 (true::counter)
  let cost := 200*(first+second+(factorWord kind factorBits).length+10)^2
  let castStore : Fin (program.extraRegisters+2) → List Bool := fun r => store (r.cast registerCount)
  match TestRun.finishWithin program (cost+1) ⟨0,castStore⟩ with
  | none => throw (IO.userError "Gaussian operation logger exceeded its proved bound")
  | some (steps,finish) =>
      unless steps≤cost && (List.finRange (program.extraRegisters+2)).all
          (fun r => finish.store r==expected (r.cast registerCount)) do
        throw (IO.userError "Gaussian operation logger changed parameters, scratch, outside state or transcript")

def tests : IO Unit := do
  for kind in [Kind.swap,.scale,.add] do
    let program := TestRun.tabulate (emit kind 2 workspace).program
    for pair in [(0,0),(1,2),(7,3),(0,1)] do
      for factor in ([0,-3/2,(2^128+1)/3] : List Rat) do
        for tail in [[],[true,false,true]] do
          checked kind program rfl pair.1 pair.2 factor tail [true,true]
  IO.println "Gaussian operation logger passed 72 whole-store executions, including coincident indices, ignored parameters and a 129-bit rational."

#eval tests
end Counting.StackMachine.GaussianTranscript.Tests
