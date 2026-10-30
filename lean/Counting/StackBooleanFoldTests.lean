import Counting.StackBooleanFold

namespace Counting.StackMachine.BooleanFold.Tests
open Routine

private def checked (routine : Routine 3) (store expected : Store 3) (cost : Nat) : IO Unit := do
  match Machine.run (step routine.program) cost ⟨0,store⟩ with
  | none => throw (IO.userError "Boolean fold stopped before its exact cost")
  | some finish =>
    unless (step routine.program finish).isNone &&
        (List.finRange 5).all (fun r => finish.store r == expected r) do
      throw (IO.userError "Boolean fold cost or whole-store contract failed")

def tests : IO Unit := do
  let cases : List (List Bool) := [[],[false],[true],[false,true],[true,false],
    [true,true,true],List.replicate 64 true,List.replicate 64 false,
    (List.replicate 128 true)++[false,true]]
  for kind in [Kind.conjunction,Kind.disjunction] do
    for value in [false,true] do
      for tail in [[],[true,false]] do
        for bits in cases do
          let store : Store 3 := ![[true,false],value::tail,[false,true,true],[],bits]
          checked (fold kind 4 1) store
            (updated 4 1 store [] (bits.foldl (operation kind) value) tail) (3*bits.length+1)
          match bits with
          | [] => pure ()
          | bit::rest =>
            checked (single kind 4 1) store (updated 4 1 store rest (operation kind value bit) tail) 3
  IO.println "Boolean folds passed 72 full-store loops and 64 single-bit updates at exact costs."

#eval tests
end Counting.StackMachine.BooleanFold.Tests
