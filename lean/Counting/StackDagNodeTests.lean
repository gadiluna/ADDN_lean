import Counting.StackDagNodeCheck
import Counting.StackEncodingPairTests

namespace Counting.StackMachine.DagValidation.NodeTests
open Routine EncodingPrograms

def base : List Executable.Node:=[⟨0,none,true,0,[]⟩,⟨0,none,false,0,[]⟩]

private def requireNode (earlier : List Executable.Node) (node : Executable.Node)
    (expected status : Bool) : IO Unit:=do
  let values:=earlier++[node]
  let current:=earlier.length
  let store : Fin 35→List Bool:=fun r=>
    if r=17 then Encoding.sequence Encoding.node values
    else if r=28 then Encoding.node.encode node
    else if r=29 then List.replicate current false
    else if r=1 then [status,true,false]
    else if r=24 then current.bits else if r=27 then [false,true,false] else []
  let vista:Executable.Vista:=⟨values.toArray,current⟩
  unless Executable.nodeValid vista current==expected do
    throw (IO.userError "Executable nodeValid expectation mismatch")
  match PairTests.runUntil nodeCheckRoutine.program 2000000 ⟨0,store⟩ with
  | none=>throw (IO.userError "Semantic serialized-node validator did not halt")
  | some (steps,result)=>
    let final:=nodeCheckStore store status [true,false] values current node
    unless (List.finRange 35).all (fun r=>result.store r==final r) do
      throw (IO.userError "Semantic node validator violated whole-store cleanup contract")
    unless result.store 1==[status && expected,true,false] do
      throw (IO.userError "Semantic node validator disagreed with actual nodeValid")
    unless steps≤901000*((store 17).length+(store 28).length+current.size+1)^5 do
      throw (IO.userError "Semantic node validator exceeded its proved bound")
    IO.println s!"Semantic nodeValid: {steps} stack instructions, status {status && expected}."

def tests : IO Unit:=do
  requireNode [] ⟨0,none,true,0,[]⟩ true true
  requireNode [] ⟨0,none,false,0,[]⟩ true true
  requireNode base ⟨0,none,false,0,[]⟩ true false
  requireNode base ⟨0,some 0,true,0,[]⟩ false true
  requireNode base ⟨0,none,true,2^128,[]⟩ false true
  requireNode base ⟨0,none,true,0,[(0,1)]⟩ false true
  requireNode base ⟨1,some 0,true,7,[(0,2^128),(1,3)]⟩ true true
  requireNode base ⟨1,some 1,false,0,[]⟩ true true
  requireNode base ⟨1,some 1,true,0,[]⟩ false true
  requireNode base ⟨1,none,true,0,[]⟩ false true
  requireNode base ⟨1,some (2^128),true,0,[]⟩ false true
  requireNode base ⟨1,some 0,true,0,[(0,0)]⟩ false true
  requireNode base ⟨1,some 0,true,0,[(1,1),(0,1)]⟩ false true
  requireNode base ⟨1,some 0,true,0,[(0,1),(0,2)]⟩ false true
  requireNode base ⟨1,some 0,true,0,[(2,1)]⟩ false true
  requireNode [⟨0,none,true,0,[]⟩,⟨1,some 0,true,1,[(0,1)]⟩]
    ⟨2,some 1,true,2,[(1,5)]⟩ true true
  requireNode base ⟨2^128,some 0,true,0,[]⟩ false true
  IO.println "Semantic node validator passed 17 full-store cases against Executable.nodeValid."

#eval tests
end Counting.StackMachine.DagValidation.NodeTests
