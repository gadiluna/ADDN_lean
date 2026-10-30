import Counting.MachineArithmeticSignedMultiply

namespace Counting.Machine.SignedMultiplyTests

def finishWithin (program : Program) : Nat → Nat → Config program → Option (Nat × Config program)
  | 0, _, _ => none
  | fuel+1, steps, config => match step program config with
    | none => some (steps,config)
    | some next => finishWithin program fuel (steps+1) next

private def requireRun (name : String) (input expected : List Bool) : IO Unit := do
  let fuel := 2000000
  match finishWithin signedProductProgram fuel 0 (initial signedProductProgram input) with
  | none => throw (IO.userError s!"Signed product exhausted {fuel} transitions: {name}")
  | some (steps,result) =>
      let right := result.tape.head :: result.tape.right
      let clean := result.tape.left.all (· == .blank) &&
        right.take expected.length == expected.map bitSymbol &&
        (right.drop expected.length).all (· == .blank)
      unless clean do throw (IO.userError s!"Signed product incorrect or dirty tape: {name}")
      unless steps ≤ 300000*(input.length+1)^6 do
        throw (IO.userError s!"Signed product exceeds proved bound: {name}")
      IO.println s!"Signed product {name}: {steps} actual transitions, clean output."

def tests : IO Unit := do
  let pair := Encoding.product Encoding.integer Encoding.integer
  for (a,b) in ([(0,0),(7,1),(-7,-1),(7,-1),(-7,1),(1,-7),(-1,7),(31,-31),(-31,31),(-64,63)] : List (Int×Int)) do
    requireRun s!"{a}*{b}" (pair.encode (a,b)) (Encoding.integer.encode (a*b))
  requireRun "empty malformed" [] (Encoding.integer.encode 0)
  requireRun "negative sign with truncated magnitude" [true,true] (Encoding.integer.encode 0)
  requireRun "truncated second operand" (Encoding.integer.encode (-3)++[true,true]) (Encoding.integer.encode 0)
  requireRun "negative zero and redundant high zeroes"
    (true::Encoding.frame [false,false]++false::Encoding.frame [true,false,false]) (Encoding.integer.encode 0)
  requireRun "valid prefix with unused suffix" (pair.encode (-5,6)++[true,true]) (Encoding.integer.encode (-30))
  IO.println "Compiled signed multiplication passed 15 sign, zero, malformed, and cleanup cases."

example : ∃ time output, time ≤ 300000*(2*(31:Int).natAbs.size+2*(-31:Int).natAbs.size+5)^6 ∧
    HaltsAt signedProductProgram ((Encoding.product Encoding.integer Encoding.integer).encode (31,-31)) time output ∧
    output.tape.denotes = Turing.Tape.mk₁ ((Encoding.integer.encode (-961)).map bitSymbol) :=
  signedProduct_integer_clean 31 (-31)

#eval tests
end Counting.Machine.SignedMultiplyTests
