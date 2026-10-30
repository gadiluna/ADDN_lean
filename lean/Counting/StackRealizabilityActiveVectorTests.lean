import Counting.StackRealizabilityActiveVector
import Counting.StackMachineTestLazy

namespace Counting.StackMachine.RealizabilityCheck.ActiveVectorTests
open Routine

def tests : IO Unit:=do
  let mut largest:=0
  let cases : List (List Bool×List Bool×List Bool×Nat):=[([],[],[],0),([],[],[],1),
    ([true],[],[],1),([],[true],[],1),([],[],[true],1),
    ([false,true,false],[true,false,false],[false,false,true],3),
    ([true],[],[false,true],4),([true,true,true],[true],[true,false],0)]
  for (newBits,oldBits,outsideBits,width) in cases do
    for flag in [[],[true,false]] do
      let store : Store 12:=fun r=>if r=0 then newBits else if r=1 then oldBits else if r=2 then outsideBits
        else if r=4 then List.replicate width false else if r=9 then flag else []
      let program:=activeVector.program
      match TestLazy.finishWithin program 100000 0 (TestLazy.empty program) ⟨0,store⟩ with
      | none=>throw (IO.userError "Active vector exceeded fuel")
      | some (time,result)=>
        let expected:=Function.update store 5 (activeValues newBits oldBits outsideBits 0 width)
        unless (List.finRange 14).all (fun r=>result.store r==expected r) do
          throw (IO.userError "Active vector violated full-store contract")
        unless time≤1000*(newBits.length+oldBits.length+outsideBits.length+width+1)^2 do
          throw (IO.userError "Active vector exceeded proved polynomial")
        largest:=max largest time
  IO.println s!"Realizability active vector passed 16 full-store cases; maximum {largest} instructions."

#eval tests
end Counting.StackMachine.RealizabilityCheck.ActiveVectorTests
