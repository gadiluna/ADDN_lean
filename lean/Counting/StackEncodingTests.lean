import Counting.StackEncodingNatural

namespace Counting.StackMachine.EncodingPrograms.Tests

/-- Run the physical, compiled single-tape machine, including bootstrap and
cleanup. These regressions supplement the general kernel proofs. -/
def finishWithin (program : Machine.Program) : Nat → Machine.Config program → Option (Nat × Machine.Config program)
  | 0, _ => none
  | fuel+1, config => match Machine.step program config with
    | none => some (0, config)
    | some next => (finishWithin program fuel next).map (fun (steps,result) => (steps+1,result))

private def requireRun (name : String) (program : Program) (coefficient : Nat)
    (input expected : List Bool) : IO Unit := do
  let machine := Compiler.compile program
  match finishWithin machine 300000 (Machine.initial machine input) with
  | none => throw (IO.userError s!"Encoding test exhausted physical transitions: {name}")
  | some (steps,result) =>
    let right := result.tape.head :: result.tape.right
    let clean := result.tape.left.all (· == .blank) &&
      right.take expected.length == expected.map Machine.bitSymbol &&
      (right.drop expected.length).all (· == .blank)
    unless clean do throw (IO.userError s!"Encoding test incorrect or dirty output: {name}")
    unless steps ≤ coefficient*(input.length+1)^4 do
      throw (IO.userError s!"Encoding test exceeded proved cost: {name}")
    IO.println s!"Encoding {name}: {steps} physical transitions, clean output."

def tests : IO Unit := do
  for payload in [[], [false], [true], [true,false,true], [false,false,false,false]] do
    requireRun s!"frame {payload}" frameProgram 2420 payload (Encoding.frame payload)
    requireRun s!"unframe {payload}" (unframeProgram 0 0 1 2) 1620 (Encoding.frame payload) payload
    requireRun s!"unframe suffix {payload}" (unframeProgram 0 0 1 2) 1620
      (Encoding.frame payload++[true,false]) payload
  for malformed in [[], [true], [true,false], [true,true,true]] do
    requireRun s!"truncated {malformed}" (unframeProgram 0 0 1 2) 1620 malformed []
  for (payload, accepted) in [([],true), ([false],false), ([true],true),
      ([true,false],false), ([false,true],true), ([true,true,false],false)] do
    requireRun s!"canonical {payload}" (canonicalProgram 0 0 1) 1280 payload [accepted]
  for value in [0,1,2,3,7,8] do
    requireRun s!"natural {value}" (naturalProgram 0 0 1) 1280 (Encoding.natural.encode value) [true]
  for malformed in [[], [true], [true,false], Encoding.frame [false], Encoding.frame [true,false],
      Encoding.natural.encode 0++[false], Encoding.natural.encode 3++[true]] do
    requireRun s!"invalid natural {malformed}" (naturalProgram 0 0 1) 1280 malformed [false]
  IO.println "Encoding primitives passed 38 compiled-machine boundary and cleanup cases."

example : canonicalPayload [] = true := rfl
example : canonicalPayload [false] = false := rfl
example : naturalCheck true (Encoding.frame [false]) = false := rfl
example : naturalCheck true (Encoding.natural.encode 7) = true := naturalCheck_encode 7
example : naturalCheck true [false,false] = false := rfl

#eval tests
end Counting.StackMachine.EncodingPrograms.Tests
