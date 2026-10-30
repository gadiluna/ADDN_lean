import Counting.StackLookupPreserving
import Counting.BinaryEuclidIterations

namespace Counting.StackMachine.Lookup.Tests

/-- Exercise arbitrary role placement and an unrelated nonempty register. -/
def roles : Fin 7 ↪ Fin 8 where
  toFun r := ![5,0,7,2,1,6,4] r
  inj' := by decide

def testStore (input index : List Bool) : Fin 8 → List Bool := fun r =>
  if r=roles 0 then input else if r=roles 1 then index else
  if r=roles 2 then [false,true] else if r=roles 3 then [true,false] else
  if r=3 then [true,true,false] else []

private def requireLookup (input index : List Bool) : IO Unit := do
  let routine := preservingLookup 1 roles
  let store := testStore input index
  let answer := input[index.length]?
  let expected := Function.update (Function.update store (roles 2) (answer.toList++store (roles 2)))
    (roles 3) (answer.isSome::store (roles 3))
  let cost := lookupCost input index
  match Machine.run (step routine.program) cost ⟨0,store⟩ with
  | none => throw (IO.userError "Lookup stopped before exact cost")
  | some finish =>
      unless (step routine.program finish).isNone do
        throw (IO.userError "Lookup exceeded its exact cost")
      unless (List.finRange 8).all (fun r => finish.store r == expected r) do
        throw (IO.userError "Lookup changed a preserved register or confused missing/false")
      unless cost ≤ 6*input.length+7*index.length+13 do
        throw (IO.userError "Lookup exceeded the proved linear bound")

def tests : IO Unit := do
  let samples : List (List Bool) := [[],[false],[true],[false,true],[true,false],
    [false,false,false],[true,false,true,false],[false,true,false,true,true]]
  let indices : List (List Bool) := [[],[false],[true],[false,true],List.replicate 5 false,List.replicate 32 true]
  for input in samples do
    for index in indices do
      requireLookup input index
  IO.println "Lookup passed 48 exact-cost cases: missing/false, mixed index bits, out-of-range, arbitrary roles and preservation."

example (a b : Nat) : Binary.euclidIter (2*Nat.size b+1) a b=(Nat.gcd a b,0) :=
  Binary.euclidIter_size_bound a b

#eval tests
end Counting.StackMachine.Lookup.Tests
