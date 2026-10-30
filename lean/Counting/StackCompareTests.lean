import Counting.StackCompareLengthPreserving
import Counting.MachineNormalize

namespace Counting.StackMachine.Compare.Tests

/-- A nontrivial embedding tests arbitrary register locations, not only the
layout used by a particular parser. Registers 3 and 5 are unrelated data. -/
def roles : Fin 6 ↪ Fin 8 where
  toFun r := ![4,0,7,2,6,1] r
  inj' := by decide

def testStore (a b : List Bool) : Fin 8 → List Bool := fun r =>
  if r=roles 0 then a else if r=roles 1 then b else
  if r=roles 2 then [false,true] else if r=3 then [true,false,true] else
  if r=5 then [false,false] else []

private def requireStore (name : String) (routine : Routine 6)
    (store expected : Fin 8 → List Bool) (cost : Nat) : IO Unit := do
  match Machine.run (step routine.program) cost ⟨0,store⟩ with
  | none => throw (IO.userError s!"Comparison stopped before exact cost: {name}")
  | some finish =>
      unless (step routine.program finish).isNone do
        throw (IO.userError s!"Comparison exceeded exact cost: {name}")
      unless (List.finRange 8).all (fun r => finish.store r == expected r) do
        throw (IO.userError s!"Comparison wrong output or changed unrelated register: {name}")

def stackTests : IO Unit := do
  let samples : List (List Bool) := [[],[false],[true],[false,false],[false,true],[true,false],
    [true,false,true],[true,false,true,false]]
  for a in samples do
    for b in samples do
      let store := testStore a b
      let eqResult := Function.update store (roles 2) (decide (a=b)::store (roles 2))
      let leResult := Function.update store (roles 2) (decide (a.length≤b.length)::store (roles 2))
      requireStore s!"equality {a} {b}" (preservingEquality 2 roles) store eqResult (preservingCost a b)
      requireStore s!"unary order {a} {b}" (preservingLengthLE 2 roles) store leResult (preservingLengthCost a b)
  IO.println "Comparison: 128 exact-cost runs passed, with preserved operands, output suffix and unrelated registers."

def finishWithin (program : Machine.Program) : Nat → Nat → Machine.Config program → Option (Nat × Machine.Config program)
  | 0, _, _ => none
  | fuel+1, elapsed, config => match Machine.step program config with
    | none => some (elapsed,config)
    | some next => finishWithin program fuel (elapsed+1) next

def machineTests : IO Unit := do
  let samples : List (List Bool) := [[],[false],[false,false,false],[true],[true,false],
    [false,true,false],[true,true,true,false,false],List.replicate 32 false,
    [true]++List.replicate 32 false]
  for input in samples do
    let expected := Encoding.natural.encode (Encoding.value input)
    match finishWithin Machine.normalizationProgram 200000 0 (Machine.initial Machine.normalizationProgram input) with
    | none => throw (IO.userError "Normalization exhausted physical-step fuel")
    | some (steps,result) =>
        let right := result.tape.head::result.tape.right
        let clean := result.tape.left.all (· == .blank) &&
          right.take expected.length == expected.map Machine.bitSymbol &&
          (right.drop expected.length).all (· == .blank)
        unless clean do throw (IO.userError "Normalization incorrect or dirty tape")
        unless steps ≤ 1620*(input.length+1)^2 do
          throw (IO.userError "Normalization exceeded its proved physical-step bound")
  IO.println "Normalization: 9 physical-machine runs passed, including long redundant-zero payloads and entire-tape cleanup."

#eval stackTests
#eval machineTests
end Counting.StackMachine.Compare.Tests
