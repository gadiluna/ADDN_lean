import Counting.MachineRationalNormalize

namespace Counting.Machine.RationalNormalizationTests
open StackMachine.RationalArithmetic

private def stackFinish (program : StackMachine.Program) :
    Nat → Nat → StackMachine.Config program → Option (Nat × StackMachine.Config program)
  | 0, _, _ => none
  | fuel+1, steps, config => match StackMachine.step program config with
    | none => some (steps,config)
    | some next => stackFinish program fuel (steps+1) next

private def machineFinish (program : Program) : Nat → Nat → Config program → Option (Nat × Config program)
  | 0, _, _ => none
  | fuel+1, steps, config => match step program config with
    | none => some (steps,config)
    | some next => machineFinish program fuel (steps+1) next

private def requireStack (sign : Bool) (numerator denominator : Nat) (suffix : List Bool) : IO Unit := do
  let input := sign::(Encoding.natural.encode numerator++Encoding.natural.encode denominator++suffix)
  let expected := Encoding.rational.encode (mkRat (Encoding.signedValue sign numerator) denominator)
  let program := completeNormalization.program
  match stackFinish program 2000000 0 (StackMachine.initial program input) with
  | none => throw (IO.userError "Rational normalization stack test exhausted its budget")
  | some (steps,result) =>
    let expectedStore := file numerator.bits expected (Nat.gcd numerator denominator).bits [] [] []
    unless (List.finRange 16).all (fun r => result.store r == expectedStore r) do
      throw (IO.userError s!"Rational normalization full-store mismatch: {sign}, {numerator}/{denominator}")
    unless steps ≤ 1500000*(input.length+1)^3 do
      throw (IO.userError "Rational normalization exceeded stack bound")
    IO.println s!"Rational normalization {sign}, {numerator}/{denominator}: {steps} stack instructions; all registers checked."

private def requireMachine (name : String) (input : List Bool) (expected : Rat) : IO Unit := do
  let word := Encoding.rational.encode expected
  match machineFinish rationalNormalizationProgram 10000000 0 (initial rationalNormalizationProgram input) with
  | none => throw (IO.userError s!"Rational normalization exhausted physical test budget: {name}")
  | some (steps,result) =>
    let right := result.tape.head::result.tape.right
    unless result.tape.left.all (· == .blank) && right.take word.length == word.map bitSymbol &&
        (right.drop word.length).all (· == .blank) do
      throw (IO.userError s!"Rational normalization incorrect output or dirty tape: {name}")
    unless steps ≤ (20*(1500000+14+5)^2)*(input.length+1)^6 do
      throw (IO.userError s!"Rational normalization exceeded physical bound: {name}")
    IO.println s!"Rational normalization {name}: {steps} physical transitions, clean tape."

def tests : IO Unit := do
  for (sign,n,d) in ([(false,0,1),(true,0,1),(false,0,0),(true,7,0),
      (false,2,4),(true,3,6),(false,17,13),(true,144,89),
      (false,2^128,2^64),(true,2^128+1,1)] : List (Bool×Nat×Nat)) do
    requireStack sign n d []
    requireStack sign n d [true,false,true]
  requireMachine "empty malformed" [] 0
  requireMachine "truncated magnitude" [true,true] 0
  requireMachine "zero denominator" (true::(Encoding.natural.encode 7++Encoding.natural.encode 0)) 0
  requireMachine "positive reduction" (false::(Encoding.natural.encode 2++Encoding.natural.encode 4)) (1/2)
  requireMachine "negative reduction" (true::(Encoding.natural.encode 3++Encoding.natural.encode 6)) (-1/2)
  requireMachine "negative zero, redundant high zeroes"
    (true::(Encoding.frame [false,false]++Encoding.frame [true,false,false])) 0
  requireMachine "valid prefix, unused suffix"
    (false::(Encoding.natural.encode 1++Encoding.natural.encode 1++[true,true])) 1
  IO.println "Rational normalization passed 20 full-store and 7 physical-machine cases."

example : normalizationFunction (true::(Encoding.natural.encode 6++Encoding.natural.encode 8)) =
    Encoding.rational.encode (mkRat (-6) 8) := by
  simpa [Encoding.signedValue] using normalizationFunction_raw true 6 8 []

#eval tests
end Counting.Machine.RationalNormalizationTests
