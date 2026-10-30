import Counting.MachineRationalPredicates
import Counting.MachineRationalToNat
import Counting.MachineRationalNegation

namespace Counting.Machine.RationalPredicateTests
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
    let input := Encoding.rational.encode value
    for (kind,name) in [(Kind.zero,"zero"),(.negative,"negative"),(.positive,"positive"),(.integral,"integral")] do
      requireRun (rationalPredicateProgram kind) s!"{name}({value})" input
        (Encoding.boolean.encode (rationalPredicateSpec kind value))
    requireRun rationalToNatProgram s!"num.toNat({value})" input (Encoding.natural.encode value.num.toNat)
  for value in ([0,-1/2,3/4] : List Rat) do
    requireRun rationalNegationProgram s!"negate({value})" (Encoding.rational.encode value) (Encoding.rational.encode (-value))
  IO.println "48 rational predicate, extraction, and negation cases passed."

#eval tests
end Counting.Machine.RationalPredicateTests
