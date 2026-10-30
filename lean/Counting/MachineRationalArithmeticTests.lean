import Counting.MachineRationalProduct
import Counting.MachineRationalAddition

namespace Counting.Machine.RationalArithmeticTests

def finishWithin (program : Program) : Nat → Nat → Config program → Option (Nat × Config program)
  | 0, _, _ => none
  | fuel+1, steps, config => match step program config with
    | none => some (steps,config)
    | some next => finishWithin program fuel (steps+1) next

private def requireRun (program : Program) (name : String) (input expected : List Bool) : IO Unit := do
  let fuel := 12000000
  match finishWithin program fuel 0 (initial program input) with
  | none => throw (IO.userError s!"Rational arithmetic exhausted {fuel} transitions: {name}")
  | some (steps,result) =>
      let right := result.tape.head :: result.tape.right
      let clean := result.tape.left.all (· == .blank) &&
        right.take expected.length == expected.map bitSymbol &&
        (right.drop expected.length).all (· == .blank)
      unless clean do throw (IO.userError s!"Rational arithmetic incorrect or dirty tape: {name}")
      IO.println s!"Rational {name}: {steps} actual transitions, clean output."

def tests : IO Unit := do
  let pair := Encoding.product Encoding.rational Encoding.rational
  for (a,b) in ([(0,0),(0,5/2),(1/2,1/3),(-1/2,1/3),(-3/4,3/4),(-6/7,-14/15),(7/8,15/16),(5,3)] : List (Rat×Rat)) do
    requireRun rationalProductProgram s!"{a}*{b}" (pair.encode (a,b)) (Encoding.rational.encode (a*b))
    requireRun rationalAdditionProgram s!"{a}+{b}" (pair.encode (a,b)) (Encoding.rational.encode (a+b))
  for input in [[],[true,true],Encoding.rational.encode (3/4)++[true,true]] do
    requireRun rationalProductProgram "malformed/truncated" input (Encoding.rational.encode 0)
    requireRun rationalAdditionProgram "malformed/truncated" input (Encoding.rational.encode 0)
  let unreduced := true::(Encoding.frame [false,true,true,false]++Encoding.frame [false,false,false,true,false]++
    Encoding.rational.encode (3/5))
  requireRun rationalProductProgram "redundant bits and unreduced fractions" unreduced (Encoding.rational.encode (-9/20))
  requireRun rationalAdditionProgram "redundant bits and unreduced fractions" unreduced (Encoding.rational.encode (-3/20))
  let suffixInput := pair.encode (-5/6,3/10)++[true,true,false]
  requireRun rationalProductProgram "ignored suffix" suffixInput (Encoding.rational.encode (-1/4))
  requireRun rationalAdditionProgram "ignored suffix" suffixInput (Encoding.rational.encode (-8/15))
  IO.println "Compiled rational addition and multiplication passed 26 finite-machine cleanup cases."

example : ∃ time output,
    time ≤ (20*(3000000+18+5)^2)*(((Encoding.product Encoding.rational Encoding.rational).encode ((-3/4:Rat),3/4)).length+1)^6 ∧
    HaltsAt rationalProductProgram ((Encoding.product Encoding.rational Encoding.rational).encode ((-3/4:Rat),3/4)) time output ∧
    output.tape.denotes = Turing.Tape.mk₁ ((Encoding.rational.encode (-9/16)).map bitSymbol) :=
  by simpa only [show (-3/4:Rat)*(3/4) = -9/16 by norm_num] using rationalProduct_rationals_clean (-3/4) (3/4)

#eval tests
end Counting.Machine.RationalArithmeticTests
