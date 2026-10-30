import Counting.MachineFramedCompare

namespace Counting.StackMachine.Compare.Framed.Tests

def finishWithin (program : Machine.Program) : Nat → Nat → Machine.Config program → Option (Nat × Machine.Config program)
  | 0, _, _ => none
  | fuel+1, elapsed, config => match Machine.step program config with
    | none => some (elapsed,config)
    | some next => finishWithin program fuel (elapsed+1) next

private def requireRun (kind : Kind) (input : List Bool) (expected : Bool) : IO Unit := do
  let machine := Compiler.compile (routine kind).program
  match finishWithin machine 300000 0 (Machine.initial machine input) with
  | none => throw (IO.userError "Framed comparison exhausted physical-transition fuel")
  | some (steps,result) =>
      let right := result.tape.head::result.tape.right
      let clean := result.tape.left.all (· == .blank) &&
        right.take 1 == [Machine.bitSymbol expected] && (right.drop 1).all (· == .blank)
      unless clean do throw (IO.userError s!"Incorrect or dirty framed comparison: {reprStr kind}, {input}")
      unless steps ≤ 32000*(input.length+1)^2 do
        throw (IO.userError "Framed comparison exceeded its proved bound")

def tests : IO Unit := do
  let cases : List (List Bool × List Bool × Bool × Bool) :=
    [([],[],true,true), ([],[true],false,true), ([false],[false],true,true),
     ([true],[false],false,true), ([true,false],[true],false,false),
     ([true,false,true],[true,false,true],true,true)]
  for (a,b,equal,lengthLE) in cases do
    let input := Encoding.frame a++Encoding.frame b
    requireRun .equality input equal
    requireRun .lengthLE input lengthLE
    requireRun .equality (input++[false]) false
    requireRun .lengthLE (input++[false]) false
  for input in [[],[true],[false],[false,true],[true,true,false],[true,false]] do
    requireRun .equality input false
    requireRun .lengthLE input false
  IO.println "Framed comparisons: 36 physical-machine cases passed, including both parse failures, trailing data, unequal lengths, and clean tapes."

#eval tests
end Counting.StackMachine.Compare.Framed.Tests
