import Counting.MachineArithmeticAddition

namespace Counting.Machine.AdditionTests

/-- Execute the compiled single-tape machine, counting actual transitions. -/
def finishWithin (program : Program) : Nat → Config program → Option (Nat × Config program)
  | 0, _ => none
  | fuel+1, config => match step program config with
    | none => some (0,config)
    | some next => (finishWithin program fuel next).map (fun (steps,result) => (steps+1,result))

private def requireRun (name : String) (input expected : List Bool) : IO Unit := do
  let fuel := 200000
  match finishWithin additionProgram fuel (initial additionProgram input) with
  | none => throw (IO.userError s!"Addition test exhausted {fuel} transitions: {name}")
  | some (steps,result) =>
      let right := result.tape.head :: result.tape.right
      let clean := result.tape.left.all (· == .blank) &&
        right.take expected.length == expected.map bitSymbol &&
        (right.drop expected.length).all (· == .blank)
      unless clean do throw (IO.userError s!"Addition test incorrect or dirty tape: {name}")
      unless steps ≤ 8820*(input.length+1)^2 do
        throw (IO.userError s!"Addition test exceeds proved bound: {name}")
      IO.println s!"Addition {name}: {steps} actual transitions, clean output."

def tests : IO Unit := do
  let pair := Encoding.product Encoding.natural Encoding.natural
  for (a,b) in [(0,0),(7,1),(31,1),(23,45),(0,19),(63,63)] do
    requireRun s!"{a}+{b}" (pair.encode (a,b)) (Encoding.natural.encode (a+b))
  requireRun "empty malformed" [] (Encoding.natural.encode 0)
  requireRun "truncated first frame" [true] (Encoding.natural.encode 0)
  requireRun "truncated second frame" (Encoding.natural.encode 3++[true]) (Encoding.natural.encode 0)
  requireRun "redundant high zeroes"
    (Encoding.frame [true,false,false]++Encoding.frame [false,false]) (Encoding.natural.encode 1)
  requireRun "valid prefix with unused suffix" (pair.encode (5,6)++[true,true]) (Encoding.natural.encode 11)
  IO.println "Compiled binary addition passed 11 boundary, carry, framing, and cleanup cases."

example : ∃ transitions output, transitions ≤ 8820*(2*(7:Nat).size+2*(1:Nat).size+3)^2 ∧
    HaltsAt additionProgram ((Encoding.product Encoding.natural Encoding.natural).encode (7,1)) transitions output ∧
    output.tape.denotes = Turing.Tape.mk₁ ((Encoding.natural.encode 8).map bitSymbol) :=
  addition_natural_clean 7 1

#eval tests
end Counting.Machine.AdditionTests
