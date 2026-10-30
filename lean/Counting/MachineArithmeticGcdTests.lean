import Counting.MachineArithmeticGcd

namespace Counting.Machine.GcdTests

/-- Tail-recursive execution of actual transitions of the compiled machine. -/
def finishWithin (program : Program) : Nat → Nat → Config program → Option (Nat × Config program)
  | 0, _, _ => none
  | fuel+1, steps, config => match step program config with
    | none => some (steps,config)
    | some next => finishWithin program fuel (steps+1) next

private def requireRun (name : String) (input expected : List Bool) : IO Unit := do
  let fuel := 5000000
  match finishWithin gcdProgram fuel 0 (initial gcdProgram input) with
  | none => throw (IO.userError s!"Gcd test exhausted {fuel} transitions: {name}")
  | some (steps,result) =>
      let right := result.tape.head :: result.tape.right
      let clean := result.tape.left.all (· == .blank) &&
        right.take expected.length == expected.map bitSymbol &&
        (right.drop expected.length).all (· == .blank)
      unless clean do throw (IO.userError s!"Gcd test incorrect or dirty tape: {name}")
      unless steps ≤ 20808000*(input.length+1)^6 do
        throw (IO.userError s!"Gcd test exceeds proved bound: {name}")
      IO.println s!"Gcd {name}: {steps} actual transitions, clean output."

def tests : IO Unit := do
  let pair := Encoding.product Encoding.natural Encoding.natural
  for (a,b) in [(0,0),(0,19),(19,0),(48,18),(17,13),(55,34),(144,89),(64,32),(21,14)] do
    requireRun s!"gcd({a},{b})" (pair.encode (a,b)) (Encoding.natural.encode (Nat.gcd a b))
  requireRun "empty malformed" [] (Encoding.natural.encode 0)
  requireRun "truncated first frame" [true] (Encoding.natural.encode 0)
  requireRun "truncated second frame" (Encoding.natural.encode 3++[true]) (Encoding.natural.encode 3)
  requireRun "redundant high zeroes"
    (Encoding.frame [true,false,false]++Encoding.frame [true,true,false]) (Encoding.natural.encode 1)
  requireRun "valid prefix with unused suffix" (pair.encode (5,6)++[true,true]) (Encoding.natural.encode 1)
  IO.println "Compiled binary gcd passed 14 boundary, remainder, framing, and cleanup cases."

example : ∃ transitions output, transitions ≤ 20808000*(2*(48:Nat).size+2*(18:Nat).size+3)^6 ∧
    HaltsAt gcdProgram ((Encoding.product Encoding.natural Encoding.natural).encode (48,18)) transitions output ∧
    output.tape.denotes = Turing.Tape.mk₁ ((Encoding.natural.encode 6).map bitSymbol) :=
  gcd_natural_clean 48 18

#eval tests
end Counting.Machine.GcdTests
