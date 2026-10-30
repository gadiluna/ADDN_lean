import Counting.MachineFramedNumericCompare

namespace Counting.StackMachine.Compare.NumericFramed.Tests

def finishWithin (program : Machine.Program) : Nat → Nat → Machine.Config program → Option (Nat × Machine.Config program)
  | 0, _, _ => none
  | fuel+1, elapsed, config => match Machine.step program config with
    | none => some (elapsed,config)
    | some next => finishWithin program fuel (elapsed+1) next

private def requireRun (input : List Bool) (expected : Bool) : IO Unit := do
  let machine := Compiler.compile routine.program
  match finishWithin machine 300000 0 (Machine.initial machine input) with
  | none => throw (IO.userError "Numeric framed comparison exhausted physical-transition fuel")
  | some (steps,result) =>
      let right := result.tape.head::result.tape.right
      let clean := result.tape.left.all (· == .blank) &&
        right.take 1 == [Machine.bitSymbol expected] && (right.drop 1).all (· == .blank)
      unless clean do throw (IO.userError s!"Incorrect or dirty numeric comparison: {input}")
      unless steps ≤ 32000*(input.length+1)^2 do
        throw (IO.userError "Numeric comparison exceeded its proved physical-step bound")

def tests : IO Unit := do
  for (a,b) in [(0,0),(1,0),(0,1),(3,7),(8,7),(15,15),(16,15),(15,16),(2,1),(2,2)] do
    requireRun ((Encoding.product Encoding.natural Encoding.natural).encode (a,b)) (a≤b)
  requireRun (Encoding.frame [false,false]++Encoding.frame []) true
  requireRun (Encoding.frame [true,false,false]++Encoding.frame [false,true]) true
  requireRun (Encoding.frame [false,true]++Encoding.frame [true,false,false]) false
  for input in [[],[false],[true],[false,true],Encoding.frame []++Encoding.frame []++[false]] do
    requireRun input false
  IO.println "Framed numeric order: 18 physical-machine cases passed, including different widths, noncanonical payloads, invalid frames, trailing bits and clean tapes."

#eval tests
end Counting.StackMachine.Compare.NumericFramed.Tests
