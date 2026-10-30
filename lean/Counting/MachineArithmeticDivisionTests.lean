import Counting.MachineArithmeticDivision

namespace Counting.Machine.DivisionTests

/-- Tail-recursive execution of actual transitions of the compiled machine. -/
def finishWithin (program : Program) : Nat → Nat → Config program → Option (Nat × Config program)
  | 0, _, _ => none
  | fuel+1, steps, config => match step program config with
    | none => some (steps,config)
    | some next => finishWithin program fuel (steps+1) next

private def requireRun (name : String) (input expected : List Bool) : IO Unit := do
  let fuel := 2000000
  match finishWithin divisionProgram fuel 0 (initial divisionProgram input) with
  | none => throw (IO.userError s!"Division test exhausted {fuel} transitions: {name}")
  | some (steps,result) =>
      let right := result.tape.head :: result.tape.right
      let clean := result.tape.left.all (· == .blank) &&
        right.take expected.length == expected.map bitSymbol &&
        (right.drop expected.length).all (· == .blank)
      unless clean do throw (IO.userError s!"Division test incorrect or dirty tape: {name}")
      unless steps ≤ 800000*(input.length+1)^4 do
        throw (IO.userError s!"Division test exceeds proved bound: {name}")
      IO.println s!"Division {name}: {steps} actual transitions, clean output."

def tests : IO Unit := do
  let pair := Encoding.product Encoding.natural Encoding.natural
  for (a,b) in [(0,0),(0,19),(19,0),(31,1),(3,5),(63,7),(225,15),(48,16)] do
    requireRun s!"{a}/{b}" (pair.encode (a,b)) (Encoding.natural.encode (a/b))
  requireRun "empty malformed" [] (Encoding.natural.encode 0)
  requireRun "truncated first frame" [true] (Encoding.natural.encode 0)
  requireRun "truncated second frame" (Encoding.natural.encode 3++[true]) (Encoding.natural.encode 0)
  requireRun "redundant high zeroes"
    (Encoding.frame [true,false,false]++Encoding.frame [true,true,false]) (Encoding.natural.encode 0)
  requireRun "valid prefix with unused suffix" (pair.encode (5,6)++[true,true]) (Encoding.natural.encode 0)
  IO.println "Compiled binary division passed 13 boundary, remainder, framing, and cleanup cases."

example : ∃ transitions output, transitions ≤ 800000*(2*(63:Nat).size+2*(7:Nat).size+3)^4 ∧
    HaltsAt divisionProgram ((Encoding.product Encoding.natural Encoding.natural).encode (63,7)) transitions output ∧
    output.tape.denotes = Turing.Tape.mk₁ ((Encoding.natural.encode 9).map bitSymbol) :=
  division_natural_clean 63 7

#eval tests
end Counting.Machine.DivisionTests
