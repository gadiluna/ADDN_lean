import Counting.StackDagRedBounds
import Counting.StackDagInitialTests

namespace Counting.StackMachine.DagValidation.RedTests
open Routine EncodingPrograms

def rootNode : Executable.Node:=⟨0,none,true,0,[]⟩
def otherNode : Executable.Node:=⟨1,some 0,false,2,[(0,2)]⟩
def values : List Executable.Node:=[rootNode,otherNode]

private def requireRed (current : Fin values.length) (targetLevel sourceIndex : Nat)
    (expected status : Bool) : IO Unit:=do
  let store : Fin 28→List Bool:=fun r=>
    if r=17 then Encoding.sequence Encoding.node values
    else if r=21 then targetLevel.bits else if r=22 then sourceIndex.bits
    else if r=25 then List.replicate current.val false
    else if r=1 then [status,true,false] else if r=23 then [false]
    else if r=27 then [true,false,true] else []
  unless redCondition values current.val targetLevel sourceIndex==expected do
    throw (IO.userError "Red-reference independent expectation mismatch")
  match PairTests.runUntil redReferenceCheck.program 1000000 ⟨0,store⟩ with
  | none=>throw (IO.userError "Red-reference checker did not halt")
  | some (steps,result)=>
    let final:=redReferenceStore store status [true,false] values current.val targetLevel sourceIndex current.isLt
    unless (List.finRange 28).all (fun r=>result.store r==final r) do
      throw (IO.userError "Red-reference checker violated whole-store contract")
    unless result.store 1==[status && expected,true,false] do
      throw (IO.userError "Red-reference checker returned the wrong status")
    unless steps≤20000*((store 17).length+sourceIndex.size+targetLevel.size+1)^4 do
      throw (IO.userError "Red-reference checker exceeded proved polynomial bound")
    IO.println s!"Red reference: {steps} stack instructions, status {status && expected}."

def tests : IO Unit:=do
  requireRed ⟨1,by decide⟩ 1 0 true true
  requireRed ⟨1,by decide⟩ 1 0 true false
  requireRed ⟨1,by decide⟩ 2 0 false true
  requireRed ⟨1,by decide⟩ (2^128) 0 false true
  requireRed ⟨1,by decide⟩ 2 1 false true
  requireRed ⟨1,by decide⟩ 1 (2^128) false true
  requireRed ⟨0,by decide⟩ 1 0 false true
  IO.println "Red-reference checker passed 7 whole-store cases, independently of source/destination leader labels."

#eval tests
end Counting.StackMachine.DagValidation.RedTests
