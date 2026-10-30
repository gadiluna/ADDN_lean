import Counting.MachineArithmeticMultiply

namespace Counting.Machine.MultiplyTests

/-- Tail-recursive execution of actual transitions of the compiled machine. -/
def finishWithin (program : Program) : Nat → Nat → Config program → Option (Nat × Config program)
  | 0, _, _ => none
  | fuel+1, steps, config => match step program config with
    | none => some (steps,config)
    | some next => finishWithin program fuel (steps+1) next

private def requireRun (name : String) (input expected : List Bool) : IO Unit := do
  let fuel := 2000000
  match finishWithin multiplicationProgram fuel 0 (initial multiplicationProgram input) with
  | none => throw (IO.userError s!"Multiplication test exhausted {fuel} transitions: {name}")
  | some (steps,result) =>
      let right := result.tape.head :: result.tape.right
      let clean := result.tape.left.all (· == .blank) &&
        right.take expected.length == expected.map bitSymbol &&
        (right.drop expected.length).all (· == .blank)
      unless clean do throw (IO.userError s!"Multiplication test incorrect or dirty tape: {name}")
      unless steps ≤ 242000*(input.length+1)^6 do
        throw (IO.userError s!"Multiplication test exceeds proved bound: {name}")
      IO.println s!"Multiplication {name}: {steps} actual transitions, clean output."

def tests : IO Unit := do
  let pair := Encoding.product Encoding.natural Encoding.natural
  for (a,b) in [(0,0),(0,19),(19,0),(1,31),(3,5),(7,9),(15,15),(16,3)] do
    requireRun s!"{a}*{b}" (pair.encode (a,b)) (Encoding.natural.encode (a*b))
  requireRun "empty malformed" [] (Encoding.natural.encode 0)
  requireRun "truncated first frame" [true] (Encoding.natural.encode 0)
  requireRun "truncated second frame" (Encoding.natural.encode 3++[true]) (Encoding.natural.encode 0)
  requireRun "redundant high zeroes"
    (Encoding.frame [true,false,false]++Encoding.frame [true,true,false]) (Encoding.natural.encode 3)
  requireRun "valid prefix with unused suffix" (pair.encode (5,6)++[true,true]) (Encoding.natural.encode 30)
  IO.println "Compiled binary multiplication passed 13 boundary, carry, framing, and cleanup cases."

example : ∃ transitions output, transitions ≤ 242000*(2*(7:Nat).size+2*(9:Nat).size+3)^6 ∧
    HaltsAt multiplicationProgram ((Encoding.product Encoding.natural Encoding.natural).encode (7,9)) transitions output ∧
    output.tape.denotes = Turing.Tape.mk₁ ((Encoding.natural.encode 63).map bitSymbol) :=
  multiplication_natural_clean 7 9

#eval tests
end Counting.Machine.MultiplyTests
