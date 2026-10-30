import Counting.StackDagRedPrefix
import Counting.StackEncodingPairTests

namespace Counting.StackMachine.DagValidation.RedPrefixTests
open Routine EncodingPrograms

def values : List Executable.Node:=[⟨0,none,true,0,[]⟩,⟨0,none,false,0,[]⟩,⟨1,some 0,false,2,[(0,1),(1,1)]⟩]

private def requirePrefix (edges : List (Nat×Nat)) (targetLevel : Nat) (expected status : Bool) : IO Unit:=do
  let suffix:=[true,false,true]
  let store : Fin 32→List Bool:=fun r=>
    if r=17 then Encoding.sequence Encoding.node values
    else if r=21 then targetLevel.bits
    else if r=28 then (Encoding.list (Encoding.product Encoding.natural Encoding.natural)).encode edges++suffix
    else if r=29 then [false,true]
    else if r=1 then [status,true,false] else if r=23 then [false]
    else if r=24 then [true,false,true] else if r=27 then [false,true,false] else []
  unless edges.all (fun edge=>redCondition values 2 targetLevel edge.1)==expected do
    throw (IO.userError "Incoming source-level expectation mismatch")
  match PairTests.runUntil redIncomingPrefix.program 2000000 ⟨0,store⟩ with
  | none=>throw (IO.userError "Incoming source-level loop did not halt")
  | some (steps,result)=>
    let final:=redPrefixStore store status [true,false] values 2 targetLevel edges suffix
    unless (List.finRange 32).all (fun r=>result.store r==final r) do
      throw (IO.userError "Incoming source-level loop violated whole-store/suffix contract")
    unless result.store 1==[status && expected,true,false] do
      throw (IO.userError "Incoming source-level loop returned the wrong accumulated status")
    unless steps≤23000*((store 17).length+(store 28).length+targetLevel.size+1)^5 do
      throw (IO.userError "Incoming source-level loop exceeded proved polynomial bound")
    IO.println s!"Incoming source levels: {steps} stack instructions, status {status && expected}."

def tests : IO Unit:=do
  requirePrefix [] 1 true true
  requirePrefix [(0,2^128),(1,3)] 1 true true
  requirePrefix [(0,1),(1,1)] 1 true false
  requirePrefix [(0,1)] 2 false true
  requirePrefix [(2,1)] 2 false true
  requirePrefix [(2^128,1)] 1 false true
  -- Ordering and positive counts are deliberately checked by incomingCheck.
  requirePrefix [(1,0),(0,0),(0,2)] 1 true true
  requirePrefix [] (2^128) true true
  IO.println "Incoming source-level scan passed 8 full-store cases with binary multiplicities and preserved suffix."

#eval tests
end Counting.StackMachine.DagValidation.RedPrefixTests
