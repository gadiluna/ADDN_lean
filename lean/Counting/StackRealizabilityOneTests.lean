import Counting.StackRealizabilityBottom
import Counting.StackDagTestRun

namespace Counting.StackMachine.RealizabilityCheck.OneTests
open Routine

private def requireOne (input : List Bool) (index : Nat) (expected accepted : Bool) : IO Unit:=do
  let store : Store 7:=![input,List.replicate index true,accepted::[false,true],[],[],[],[],[],[]]
  let wanted:=Function.update store 2 ((accepted && expected)::[false,true])
  unless decide (FieldAccess.selectPayload input index=some [true])==expected do
    throw (IO.userError "Selected count-one reference expectation mismatch")
  match DagValidation.TestRun.run countOneGuard.program 1000000 0 ⟨0,store⟩ with
  | none=>throw (IO.userError "Selected count-one scan exceeded test fuel")
  | some (steps,result)=>
    unless (List.finRange 9).all (fun r=>result.store r==wanted r) do
      throw (IO.userError "Selected count-one scan violated full-store result")
    unless steps≤60*(input.length+index+1) do
      throw (IO.userError "Selected count-one scan exceeded proved bound")
    IO.println s!"Selected count one: {steps} stack instructions, status {accepted && expected}."

def tests : IO Unit:=do
  for (values,index,expected) in [
      ([1],0,true),([2],0,false),([0],0,false),([1,2,1],0,true),([1,2,1],1,false),
      ([1,2,1],2,true),([1,2,1],3,false),([],0,false),([2^128,1],0,false),([2^128,1],1,true)] do
    requireOne ((Encoding.list Encoding.natural).encode values) (index+1) expected true
  requireOne ((Encoding.list Encoding.natural).encode [1]) 1 true false
  requireOne [] 0 false true
  requireOne [true] 0 false true
  requireOne [true,true,true] 0 false true
  requireOne (Encoding.frame [false,true]) 0 false true
  IO.println "Selected count-one check passed 15 full-store cases, including absence, zero, large values and malformed frames."

#eval tests
end Counting.StackMachine.RealizabilityCheck.OneTests
