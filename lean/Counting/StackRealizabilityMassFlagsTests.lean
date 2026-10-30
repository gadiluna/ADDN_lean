import Counting.StackRealizabilityMassFlags
import Counting.StackMachineTestLazy

namespace Counting.StackMachine.RealizabilityCheck.MassFlagsTests
open Routine

def tests : IO Unit:=do
  let mut largest:=0
  let cases : List (Nat×Nat×Nat×Nat×Nat×Nat):=[(0,0,0,0,0,0),(1,1,2,2,3,3),
    (0,1,0,1,0,1),(1,0,1,0,1,0),(2,5,7,3,4,8),(5,2,3,7,8,4),
    (2^129,2^129+1,2^130,2^129,2^100,2^101),(2^129+1,2^129,2^129,2^130,2^101,2^100)]
  for (child,weight,supply,demand,visible,order) in cases do
    for tail in [[],[true,false]] do
      let store : Store 10:=![child.bits,weight.bits,supply.bits,demand.bits,visible.bits,order.bits,
        tail,tail,tail,[],[],[]]
      let program:=massFlags.program
      match TestLazy.finishWithin program 100000 0 (TestLazy.empty program) ⟨0,store⟩ with
      | none=>throw (IO.userError "Mass flags exceeded fuel")
      | some (time,result)=>
        let expected:=massFlagsStore store child weight supply demand visible order
        unless (List.finRange 12).all (fun r=>result.store r==expected r) do
          throw (IO.userError "Mass flags violated full-store contract")
        unless time≤50*(child.size+weight.size+supply.size+demand.size+visible.size+order.size+1) do
          throw (IO.userError "Mass flags exceeded proved linear bound")
        largest:=max largest time
  IO.println s!"Realizability mass flags passed 16 full-store cases; maximum {largest} instructions."

#eval tests
end Counting.StackMachine.RealizabilityCheck.MassFlagsTests
