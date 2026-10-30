import Counting.StackDagDistinctPrefix
import Counting.StackDagTestRun

namespace Counting.StackMachine.DagValidation.DistinctTests
open Routine EncodingPrograms

private def requireDistinct (values : List Executable.Node) (expected status : Bool) : IO Unit:=do
  let suffix:=[false,true,true,false,true]
  let store : Fin 35→List Bool:=fun r=>
    if r=17 then (Encoding.list Encoding.node).encode values++suffix
    else if r=1 then [status,false,true]
    else if r=24 then [true,false,true] else []
  unless (values.eraseDups.length==values.length)==expected do
    throw (IO.userError "Duplicate-scan executable expectation mismatch")
  match TestRun.run distinctPrefixRoutine.program 10000000 0 ⟨0,store⟩ with
  | none=>throw (IO.userError "Duplicate-scan machine did not halt")
  | some (steps,result)=>
    let final:=distinctPrefixStore store status [false,true] values suffix
    unless (List.finRange 35).all (fun r=>result.store r==final r) do
      throw (IO.userError "Duplicate scan violated source/counter/workspace contract")
    unless result.store 1==[status && expected,false,true] do
      throw (IO.userError "Duplicate scan disagreed with eraseDups length")
    unless steps≤220000*((store 17).length+1)^6 do
      throw (IO.userError "Duplicate scan exceeded proved bound")
    IO.println s!"Node duplicate scan: {steps} stack instructions, status {status && expected}."

def tests : IO Unit:=do
  let a:Executable.Node:=⟨0,none,true,0,[]⟩
  let b:Executable.Node:=⟨0,none,false,0,[]⟩
  let c:Executable.Node:=⟨1,some 0,true,2^128,[(0,2^80)]⟩
  requireDistinct [] true true
  requireDistinct [a] true true
  requireDistinct [a,a] false true
  requireDistinct [a,b] true true
  requireDistinct [a,b,a] false true
  requireDistinct [a,b,b] false true
  requireDistinct [a,b,c] true true
  requireDistinct [a,c,c] false true
  requireDistinct [a,b,c] true false
  IO.println "Node duplicate scan passed 9 full-store cases including large binary labels and prior failure."

#eval tests
end Counting.StackMachine.DagValidation.DistinctTests
