import Counting.MachineRationalInverse

namespace Counting.Machine.RationalInverseTests

private def finishWithin (program : Program) : Nat → Nat → Config program → Option (Nat × Config program)
  | 0, _, _ => none
  | fuel+1, steps, config => match step program config with
    | none => some (steps,config)
    | some next => finishWithin program fuel (steps+1) next

private def requireRun (name : String) (input : List Bool) (expected : Rat) : IO Unit := do
  let word := Encoding.rational.encode expected
  match finishWithin rationalInverseProgram 2000000 0 (initial rationalInverseProgram input) with
  | none => throw (IO.userError s!"Rational inverse test exhausted its budget: {name}")
  | some (steps,result) =>
    let right := result.tape.head::result.tape.right
    unless result.tape.left.all (· == .blank) && right.take word.length == word.map bitSymbol &&
        (right.drop word.length).all (· == .blank) do
      throw (IO.userError s!"Rational inverse wrong result or dirty tape: {name}")
    unless steps ≤ (20*(1500000+14+5)^2)*(input.length+1)^6 do
      throw (IO.userError s!"Rational inverse exceeded proved bound: {name}")
    IO.println s!"Rational inverse {name}: {steps} physical transitions, clean tape."

def tests : IO Unit := do
  requireRun "empty malformed" [] 0
  requireRun "zero" (Encoding.rational.encode 0) 0
  requireRun "negative fraction" (Encoding.rational.encode (-2/3)) (-3/2)
  requireRun "unreduced positive fraction"
    (false::(Encoding.natural.encode 4++Encoding.natural.encode 2)) (1/2)
  requireRun "zero denominator"
    (true::(Encoding.natural.encode 3++Encoding.natural.encode 0)) 0
  requireRun "truncated denominator" (true::(Encoding.natural.encode 3++[true])) 0
  requireRun "redundant zero, unused suffix"
    (true::(Encoding.frame [false,false]++Encoding.natural.encode 1++[true])) 0
  IO.println "Rational inverse passed 7 physical-machine sign, zero, malformed and cleanup cases."

#eval tests
end Counting.Machine.RationalInverseTests
