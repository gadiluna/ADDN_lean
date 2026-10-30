import Counting.StackFrameReadPreserving

namespace Counting.StackMachine.FieldAccess.Tests

def roles : Fin 8 ↪ Fin 10 where
  toFun r := ![5,0,7,2,1,6,4,8] r
  inj' := by decide

def testStore (input index : List Bool) : Fin 10 → List Bool := fun r =>
  if r=roles 0 then input else if r=roles 1 then index else
  if r=roles 2 then [false,true] else if r=roles 3 then [true,false] else
  if r=3 then [true,false,true] else if r=9 then [false,false,true] else []

def finishWithin (program : Program) : Nat → Nat → Config program → Option (Nat × Config program)
  | 0, _, _ => none
  | fuel+1, steps, config => match step program config with
    | none => some (steps,config)
    | some next => finishWithin program fuel (steps+1) next

private def requireRead (input index : List Bool) : IO Unit := do
  let routine := preservingRead 2 roles
  let store := testStore input index
  let answer := selectPayload input index.length
  let expected := Function.update (Function.update store (roles 2) (answer.getD []++store (roles 2)))
    (roles 3) (answer.isSome::store (roles 3))
  let bound := 10*input.length+8*index.length+14
  match finishWithin routine.program (bound+1) 0 ⟨0,store⟩ with
  | none => throw (IO.userError "Framed lookup exceeded the proved linear bound")
  | some (time,finish) =>
      unless time ≤ bound do throw (IO.userError "Framed lookup exceeded its bound")
      unless (List.finRange 10).all (fun r => finish.store r == expected r) do
        throw (IO.userError "Framed lookup wrong field/flag or changed a preserved register")

def tests : IO Unit := do
  let lists : List (List Nat) := [[],[0],[1],[0,1,0],[3,0,7,2],[2^128,0,2^64]]
  let indices : List (List Bool) := [[],[false],[true],[false,true],List.replicate 4 false,
    List.replicate 8 true,List.replicate 40 false]
  for values in lists do
    for index in indices do
      let input := (Encoding.list Encoding.natural).encode values
      let afterHeader := false::index
      unless selectPayload input afterHeader.length == (values[index.length]?).map Nat.bits do
        throw (IO.userError "Natural-list codec offset disagrees with indexed selection")
      requireRead input afterHeader
  for input in [[],[true],[true,false],[false,true],[true,true,true],[false,false,true],
      Encoding.frame [false,false]++[true],Encoding.frame [true]++Encoding.frame []++[true]] do
    for index in indices do
      requireRead input index
  IO.println "Framed lookup passed 98 full-store cases: list headers, zero/absent distinction, 129-bit values, malformed frames, out-of-range and preserved operands."

example (values : List Nat) (index : Nat) :
    selectPayload ((Encoding.list Encoding.natural).encode values) (index+1)=
      (values[index]?).map Nat.bits := selectPayload_naturalList values index

#eval tests
end Counting.StackMachine.FieldAccess.Tests
