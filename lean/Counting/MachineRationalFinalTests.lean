import Counting.MachineRationalSubtraction
import Counting.MachineRationalPositiveIntegral

namespace Counting.Machine.RationalFinalTests
open StackMachine.RationalArithmetic.Predicates

def finishWithin (program : Program) : Nat → Nat → Config program → Option (Nat × Config program)
  | 0, _, _ => none
  | fuel+1, steps, config => match step program config with
    | none => some (steps,config)
    | some next => finishWithin program fuel (steps+1) next

private def requireRun (program : Program) (name : String) (input expected : List Bool) : IO Unit := do
  match finishWithin program 2000000 0 (initial program input) with
  | none => throw (IO.userError s!"Rational primitive exhausted fuel: {name}")
  | some (steps,result) =>
      let right := result.tape.head :: result.tape.right
      let clean := result.tape.left.all (· == .blank) &&
        right.take expected.length == expected.map bitSymbol &&
        (right.drop expected.length).all (· == .blank)
      unless clean do throw (IO.userError s!"Rational primitive incorrect or dirty tape: {name}")
      IO.println s!"Rational primitive {name}: {steps} transitions, clean output."

def tests : IO Unit := do
  for value in ([0,1,-1,1/2,-1/2,3,-3,7/4,128] : List Rat) do
    requireRun rationalPositiveIntegralProgram s!"positiveIntegral({value})" (Encoding.rational.encode value)
      (Encoding.boolean.encode (decide (value.den=1 ∧ 0<value.num)))
  for (a,b) in ([(1/2,1/3),(-3/4,-3/4),(0,5/2),(5,-3)] : List (Rat×Rat)) do
    requireRun rationalSubtractionProgram s!"{a}-{b}"
      ((Encoding.product Encoding.rational Encoding.rational).encode (a,b)) (Encoding.rational.encode (a-b))
  requireRun rationalSubtractionProgram "subtraction malformed" [] (Encoding.rational.encode 0)
  IO.println "14 scalar positive-integral and subtraction cases passed."

#eval tests
end Counting.Machine.RationalFinalTests
