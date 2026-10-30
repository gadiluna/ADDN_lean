import Counting.StackDagCoverPrefix
import Counting.StackDagTestRun

namespace Counting.StackMachine.DagValidation.CoverTests
open Routine EncodingPrograms

private def requireCover (values : List Executable.Node) (bottom : Nat) (expected status : Bool) : IO Unit:=do
  let store : Fin 35→List Bool:=fun r=>
    if r=17 then (Encoding.list Encoding.node).encode values++Encoding.natural.encode bottom
    else if r=1 then [status,false,true]
    else if r=18 then [true,false,true] else []
  let vista:Executable.Vista:=⟨values.toArray,bottom⟩
  unless Executable.backwardCoverAnyCheck vista==expected do
    throw (IO.userError "Backward-cover executable expectation mismatch")
  match TestRun.run coverPrefix.program 10000000 0 ⟨0,store⟩ with
  | none=>throw (IO.userError "Backward-cover machine did not halt")
  | some (steps,result)=>
    let final:=coverPrefixStore store status [false,true] values bottom
    unless (List.finRange 35).all (fun r=>result.store r==final r) do
      throw (IO.userError "Backward cover violated source/counter/workspace contract")
    unless result.store 1==[status && expected,false,true] do
      throw (IO.userError "Backward cover disagreed with exact reference criterion")
    unless steps≤103000*((store 17).length+1)^5 do
      throw (IO.userError "Backward cover exceeded proved bound")
    IO.println s!"Backward-cover scan: {steps} stack instructions, status {status && expected}."

def tests : IO Unit:=do
  let a:Executable.Node:=⟨0,none,true,0,[]⟩
  let b:Executable.Node:=⟨0,none,false,0,[]⟩
  let child:Executable.Node:=⟨1,some 0,true,3,[]⟩
  let red:Executable.Node:=⟨1,some 0,true,1,[(1,2^128)]⟩
  requireCover [] 0 false true
  requireCover [a] 0 true true
  requireCover [a] (2^128) false true
  requireCover [a,child] 1 true true
  requireCover [a,b] 1 false true
  requireCover [a,b,red] 2 true true
  requireCover [a,b,child] 2 false true
  requireCover [a,child] 0 false true
  requireCover [a,b,red] 2 true false
  -- A self-reference can satisfy this component; nodeValid rejects it separately.
  requireCover [⟨0,some 0,true,0,[]⟩,b] 1 true true
  IO.println "Backward cover passed 10 full-store cases; topology remains the separate node-validity check."

#eval tests
end Counting.StackMachine.DagValidation.CoverTests
