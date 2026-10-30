import Counting.StackEncodingBoundedNatural
import Counting.StackEncodingPairTests

namespace Counting.StackMachine.EncodingPrograms.BoundedNaturalTests

def roles : CountWorkspace 1 where
  toFun i:=⟨10-i.val,by omega⟩
  inj':=by
    intro a b equal
    have h:=congrArg (fun r:Fin 12=>r.val) equal
    apply Fin.ext
    have aBound:=a.isLt
    have bBound:=b.isLt
    change 10-a.val=10-b.val at h
    omega

private def requireCount (value : Nat) (budget : List Bool) : IO Unit := do
  let store : Fin 12→List Bool:=fun r=>
    if r=roles 0 then Encoding.natural.encode value else if r=roles 10 then budget
    else if r=roles 6 then [false,true] else if r=11 then [true,false,true] else []
  match PairTests.runUntil (boundedCount 1 roles).program 1000000 ⟨0,store⟩ with
  | none=>throw (IO.userError "Bounded natural conversion exceeded test budget")
  | some (steps,result)=>
    let expected:=boundedNaturalResult 1 roles store value
    unless (List.finRange 12).all (fun r=>result.store r==expected r) do
      throw (IO.userError "Bounded natural conversion violated its full-store contract")
    unless result.store (roles 1)==List.replicate (min value budget.length) true &&
        result.store (roles 6)==(decide (value≤budget.length)::[false,true]) do
      throw (IO.userError "Bounded natural conversion has the wrong cap or flag")
    unless steps≤64*(budget.length+(Encoding.natural.encode value).length+1)^3 do
      throw (IO.userError "Bounded natural conversion exceeded proved cost")
    IO.println s!"Bounded natural: {steps} stack steps, cap {min value budget.length}."

def tests : IO Unit:=do
  requireCount 0 []
  requireCount 1 []
  requireCount 0 [false,true,false]
  requireCount 2 [false,true,false]
  requireCount 3 [false,true,false]
  requireCount 4 [false,true,false]
  requireCount (2^128) [false,true,false]
  IO.println "Bounded natural conversion passed 7 canonical full-store cases with reversed roles and sentinels."

#eval tests
end Counting.StackMachine.EncodingPrograms.BoundedNaturalTests
