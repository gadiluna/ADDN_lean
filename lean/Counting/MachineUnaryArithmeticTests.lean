import Counting.MachineUnaryArithmetic

namespace Counting.Machine.UnaryTests

def finishWithin (program : Program) : Nat → Nat → Config program → Option (Nat × Config program)
  | 0, _, _ => none
  | fuel+1, elapsed, config => match step program config with
    | none => some (elapsed,config)
    | some next => finishWithin program fuel (elapsed+1) next

private def requireRun (name : String) (program : Program) (input expected : List Bool) : IO Unit := do
  match finishWithin program 1000000 0 (initial program input) with
  | none => throw (IO.userError s!"Unary arithmetic test exhausted fuel: {name}")
  | some (steps,result) =>
      let right := result.tape.head::result.tape.right
      let clean := result.tape.left.all (· == .blank) &&
        right.take expected.length == expected.map bitSymbol &&
        (right.drop expected.length).all (· == .blank)
      unless clean do throw (IO.userError s!"Unary arithmetic test incorrect or dirty tape: {name}")
      IO.println s!"Unary {name}: {steps} actual transitions, clean output."

def tests : IO Unit := do
  requireRun "empty length" unaryLengthProgram [] []
  requireRun "mixed bits length" unaryLengthProgram [false,true,false,true] [true,true,true,true]
  for n in [0,1,2,7,15,32] do
    requireRun s!"{n} to binary" unaryToBinaryProgram (List.replicate n true) n.bits
  requireRun "mixed bits counter" unaryToBinaryProgram [false,true,false,true,false] (5:Nat).bits
  IO.println "Compiled unary arithmetic passed 9 counting, carry, and cleanup cases."

#eval tests
end Counting.Machine.UnaryTests
