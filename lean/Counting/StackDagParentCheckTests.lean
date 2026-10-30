import Counting.StackDagParentBounds
import Counting.StackEncodingPairTests

namespace Counting.StackMachine.DagValidation.BinaryTests
open EncodingPrograms

def initialNode : Executable.Node:=⟨0,none,true,0,[]⟩
def nextNode : Executable.Node:=⟨1,some 0,true,2,[(0,2)]⟩
def values : List Executable.Node:=[initialNode,nextNode]

private def requireBinary (current : Fin values.length) (node : Executable.Node) (expected status : Bool) : IO Unit:=do
  let store : Fin 28→List Bool:=fun r=>
    if r=17 then Encoding.sequence Encoding.node values
    else if r=21 then node.level.bits else if r=22 then (parentCode node).bits
    else if r=23 then [node.leader] else if r=24 then current.val.bits
    else if r=25 then List.replicate current.val false
    else if r=1 then [status,true,false] else if r=27 then [true,false,true] else []
  unless parentCheck values current.val node==expected do
    throw (IO.userError "Binary parent check independent expectation mismatch")
  match PairTests.runUntil binaryParentCheck.program 1000000 ⟨0,store⟩ with
  | none=>throw (IO.userError "Binary parent semantic checker did not halt")
  | some (steps,result)=>
    let final:=binaryParentStore store status [true,false] values current.val node current.isLt
    unless (List.finRange 28).all (fun r=>result.store r==final r) do
      throw (IO.userError "Binary parent semantic checker violated whole-store contract")
    unless result.store 1==[status && expected,true,false] do
      throw (IO.userError "Binary parent semantic checker produced the wrong acceptance bit")
    unless steps≤10000*((store 17).length+(Encoding.node.encode node).length+1)^4 do
      throw (IO.userError "Binary parent semantic checker exceeded proved polynomial bound")
    IO.println s!"Binary parent check: {steps} stack instructions; status {status && expected}."

def tests : IO Unit:=do
  requireBinary ⟨1,by decide⟩ nextNode true true
  requireBinary ⟨1,by decide⟩ nextNode true false
  requireBinary ⟨1,by decide⟩ {nextNode with parent:=none} false true
  requireBinary ⟨1,by decide⟩ {nextNode with parent:=some 1} false true
  requireBinary ⟨1,by decide⟩ {nextNode with parent:=some (2^128)} false true
  requireBinary ⟨0,by decide⟩ nextNode false true
  requireBinary ⟨1,by decide⟩ {nextNode with leader:=false} false true
  IO.println "Binary parent checker passed 7 complete-store cases, including 129-bit invalid reference."

#eval tests
end Counting.StackMachine.DagValidation.BinaryTests
