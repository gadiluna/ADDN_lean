import Counting.MachineRationalEquality

namespace Counting.Machine.RationalEqualityTests
open StackMachine.RationalArithmetic.Equality

private def finishWithin (program : Program) : Nat → Nat → Config program → Option (Nat × Config program)
  | 0, _, _ => none
  | fuel+1, steps, config => match step program config with
    | none => some (steps,config)
    | some next => finishWithin program fuel (steps+1) next

private def runTest (input : List Bool) (expected : Bool) : IO Unit := do
  match finishWithin rationalEqualityProgram 20000000 0 (initial rationalEqualityProgram input) with
  | none => throw (IO.userError "Rational equality exhausted its physical test budget")
  | some (steps,output) =>
    let tape := output.tape.head::output.tape.right
    unless output.tape.left.all (· == .blank) && tape.take 1 == [bitSymbol expected] &&
        (tape.drop 1).all (· == .blank) do
      throw (IO.userError "Rational equality returned a wrong result or dirty tape")
    unless steps ≤ 250880*(input.length+1)^2 do
      throw (IO.userError "Rational equality exceeded its proved bound")
    IO.println s!"Rational equality: {input.length} bits, {steps} physical transitions, clean tape."

def tests : IO Unit := do
  let examples : List (Rat × Rat) := [(0,0),(0,1),(1,-1),(-1,-1),(2/3,4/6),
    (2/3,3/4),(-7/5,7/5),(-(2^128),-(2^128)),(2^128+1,2^128)]
  for pair in examples do
    runTest ((Encoding.product Encoding.rational Encoding.rational).encode pair) (decide (pair.1=pair.2))
  for input in [[],[true],[false,false],[false,true,false,true],List.replicate 24 true,
      (Encoding.product Encoding.rational Encoding.rational).encode ((2/3:Rat),2/3)++[true,false]] do
    runTest input (check input)
  IO.println "Rational equality passed 9 canonical and 6 total-extension physical cases."

example : check ((Encoding.product Encoding.rational Encoding.rational).encode ((2/3:Rat),4/6))=true := by
  rw [check_rationals]
  norm_num

#eval tests
end Counting.Machine.RationalEqualityTests
