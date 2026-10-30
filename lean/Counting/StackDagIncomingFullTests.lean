import Counting.StackDagIncomingFull
import Counting.StackEncodingPairTests

namespace Counting.StackMachine.DagValidation.IncomingFullTests
open Routine EncodingPrograms

def values : List Executable.Node:=[⟨0,none,true,0,[]⟩,⟨0,none,false,0,[]⟩,⟨1,some 0,false,2,[(0,1),(1,1)]⟩]

private def requireIncoming (edges : List (Nat×Nat)) (targetLevel : Nat) (expected status : Bool) : IO Unit:=do
  let suffix:=[true,false,true]
  let store : Fin 35→List Bool:=fun r=>
    if r=17 then Encoding.sequence Encoding.node values
    else if r=21 then targetLevel.bits
    else if r=28 then (Encoding.list (Encoding.product Encoding.natural Encoding.natural)).encode edges++suffix
    else if r=29 then [false,true]
    else if r=1 then [status,true,false] else if r=23 then [false]
    else if r=24 then Nat.bits 2 else if r=27 then [false,true,false] else []
  unless incomingCondition values 2 targetLevel edges==expected do
    throw (IO.userError "Complete incoming expectation mismatch")
  match PairTests.runUntil fullIncomingPrefix.program 2000000 ⟨0,store⟩ with
  | none=>throw (IO.userError "Complete incoming loop did not halt")
  | some (steps,result)=>
    let final:=fullIncomingStore store status [true,false] values 2 targetLevel edges suffix
    unless (List.finRange 35).all (fun r=>result.store r==final r) do
      throw (IO.userError "Complete incoming loop violated whole-store/suffix contract")
    unless result.store 1==[status && expected,true,false] do
      throw (IO.userError "Complete incoming loop returned the wrong accumulated status")
    unless steps≤26000*((store 17).length+(store 28).length+targetLevel.size+Nat.size 2+1)^5 do
      throw (IO.userError "Complete incoming loop exceeded proved polynomial bound")
    IO.println s!"Complete incoming check: {steps} stack instructions, status {status && expected}."

def tests : IO Unit:=do
  requireIncoming [] 1 true true
  requireIncoming [(0,2^128),(1,3)] 1 true true
  requireIncoming [(0,1),(1,1)] 1 true false
  requireIncoming [(0,1)] 2 false true
  requireIncoming [(2,1)] 2 false true
  requireIncoming [(2^128,1)] 1 false true
  requireIncoming [(0,0)] 1 false true
  requireIncoming [(1,1),(0,1)] 1 false true
  requireIncoming [(0,1),(0,2)] 1 false true
  requireIncoming [] (2^128) true true
  IO.println "Complete incoming scan passed 10 full-store cases, including zero counts, unsorted and duplicate references."

#eval tests
end Counting.StackMachine.DagValidation.IncomingFullTests
