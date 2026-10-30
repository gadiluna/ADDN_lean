import Counting.MachineRationalCast

namespace Counting.Machine.RationalBasicTests
open StackMachine

private def finishWithin (program : Machine.Program) : Nat → Nat → Machine.Config program →
    Option (Nat × Machine.Config program)
  | 0, _, _ => none
  | fuel+1, steps, config => match Machine.step program config with
    | none => some (steps,config)
    | some next => finishWithin program fuel (steps+1) next

def roles : Fin 6 ↪ Fin 8 := ⟨![4,0,6,2,5,7],by decide⟩

private def equalityTest (left right : Rat) : IO Unit := do
  let a:=Encoding.rational.encode left
  let b:=Encoding.rational.encode right
  let store : Fin 8 → List Bool := ![b,[true,false],[],[false,true],a,[],[true,true],[]]
  let expected := Function.update store 6 (decide (left=right)::[true,true])
  let program := (Compare.preservingEquality 2 roles).program
  let cost := Compare.preservingCost a b
  match Machine.run (StackMachine.step program) cost ⟨0,store⟩ with
  | none => throw (IO.userError "Rational equality halted before its exact cost")
  | some result =>
    unless (StackMachine.step program result).isNone &&
        (List.finRange 8).all (fun r => result.store r == expected r) do
      throw (IO.userError "Rational equality full-store or exact-cost mismatch")

private def castTest (payload : List Bool) (value : Nat) : IO Unit := do
  let word:=Encoding.rational.encode (value:Rat)
  match finishWithin rationalCastProgram 2000000 0 (Machine.initial rationalCastProgram payload) with
  | none => throw (IO.userError "Natural-to-rational test exhausted its budget")
  | some (steps,result) =>
    let right:=result.tape.head::result.tape.right
    unless result.tape.left.all (· == .blank) && right.take word.length == word.map bitSymbol &&
        (right.drop word.length).all (· == .blank) do
      throw (IO.userError "Natural-to-rational cast wrong value or dirty tape")
    unless steps ≤ 6480*(payload.length+1)^2 do throw (IO.userError "Natural-to-rational cast exceeded bound")
    IO.println s!"Natural-to-rational cast of {value}: {steps} physical transitions, clean tape."

def tests : IO Unit := do
  let values : List Rat := [0,1,-1,2/3,4/6,2^128,-(2^128)]
  for left in values do
    for right in values do equalityTest left right
  for value in [0,1,2,127,2^64,2^128+1] do castTest value.bits value
  castTest (List.replicate 64 false) 0
  castTest (true::List.replicate 32 false) 1
  IO.println "Rational primitives passed 49 full-store equality and 8 physical cast cases."

#eval tests
end Counting.Machine.RationalBasicTests
