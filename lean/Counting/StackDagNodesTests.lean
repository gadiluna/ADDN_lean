import Counting.StackDagNodesPrefix
import Counting.StackEncodingPairTests

namespace Counting.StackMachine.DagValidation.NodesTests
open Routine EncodingPrograms

private def requireNodes (values : List Executable.Node) (expected status : Bool) : IO Unit:=do
  let suffix:=[true,false,true,false]
  let store : Fin 35→List Bool:=fun r=>
    if r=17 then (Encoding.list Encoding.node).encode values++suffix
    else if r=1 then [status,false,true] else []
  let vista:Executable.Vista:=⟨values.toArray,0⟩
  unless (List.range values.length).all (Executable.nodeValid vista)==expected do
    throw (IO.userError "All-node executable component expectation mismatch")
  match PairTests.runUntil nodesPrefixRoutine.program 10000000 ⟨0,store⟩ with
  | none=>throw (IO.userError "All-node semantic loop did not halt")
  | some (steps,result)=>
    let final:=nodesPrefixStore store status [false,true] values suffix
    unless (List.finRange 35).all (fun r=>result.store r==final r) do
      throw (IO.userError "All-node semantic loop violated source/counter/workspace contract")
    unless result.store 1==[status && expected,false,true] do
      throw (IO.userError "All-node semantic loop disagreed with executable all nodeValid")
    unless steps≤222000000*((store 17).length+1)^6 do
      throw (IO.userError "All-node semantic loop exceeded proved bound")
    IO.println s!"All-node semantic scan: {steps} stack instructions, status {status && expected}."

def tests : IO Unit:=do
  requireNodes [] true true
  requireNodes [⟨0,none,true,0,[]⟩] true true
  -- Empty tables and duplicate nodes are rejected by separate global checks.
  requireNodes [⟨0,none,true,0,[]⟩,⟨0,none,true,0,[]⟩] true true
  requireNodes [⟨0,none,true,0,[]⟩,⟨1,some 0,true,5,[(0,2^80)]⟩] true true
  requireNodes [⟨0,none,true,0,[]⟩,⟨1,some 0,true,1,[(0,1)]⟩,⟨2,some 1,true,1,[(1,1)]⟩] true false
  requireNodes [⟨0,none,true,0,[]⟩,⟨1,some 0,false,1,[(0,1)]⟩] false true
  requireNodes [⟨0,none,true,0,[]⟩,⟨1,some 0,true,1,[(0,0)]⟩] false true
  requireNodes [⟨0,none,true,0,[]⟩,⟨1,some 0,true,1,[(0,1),(0,1)]⟩] false true
  IO.println "All-node semantic validation passed 8 full-store cases against the actual nodeValid loop."

#eval tests
end Counting.StackMachine.DagValidation.NodesTests
