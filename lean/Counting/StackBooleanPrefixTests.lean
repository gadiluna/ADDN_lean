import Counting.StackBooleanPrefix

namespace Counting.StackMachine.BooleanFold.PrefixTests
open Routine

private def checked (kind : Kind) (bits suffix : List Bool) (value : Bool) (tail : List Bool) : IO Unit := do
  let routine := prefixRoutine (registers := 3) kind 4 1 2
  let store : Store 3 := ![[true,false],value::tail,List.replicate bits.length true,[false,true],bits++suffix]
  let expected := prefixStore 4 1 2 store suffix (bits.foldl (operation kind) value) tail
  match Machine.run (step routine.program) (5*bits.length+1) ⟨0,store⟩ with
  | none => throw (IO.userError "Boolean prefix halted before its exact cost")
  | some finish =>
    unless (step routine.program finish).isNone &&
        (List.finRange 5).all (fun r => finish.store r==expected r) do
      throw (IO.userError "Boolean prefix whole-store or exact-cost mismatch")

def tests : IO Unit := do
  let cases : List (List Bool) := [[],[false],[true],[false,true],[true,false],[true,true,true],
    List.replicate 64 true,List.replicate 64 false,(List.replicate 128 true)++[false,true]]
  for kind in [Kind.conjunction,Kind.disjunction] do
    for value in [false,true] do
      for tail in [[],[true,false]] do
        for suffix in [[],[true,false,true]] do
          for bits in cases do checked kind bits suffix value tail
  IO.println "Boolean prefix passed 144 whole-store executions with exact costs and preserved suffixes."

#eval tests
end Counting.StackMachine.BooleanFold.PrefixTests
