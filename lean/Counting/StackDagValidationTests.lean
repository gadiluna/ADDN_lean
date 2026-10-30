import Counting.StackDagParentLookup
import Counting.StackDagParentIndex
import Counting.StackEncodingPairTests

namespace Counting.StackMachine.DagValidation.Tests
open EncodingPrograms

def initialNode : Executable.Node:=⟨0,none,true,0,[]⟩
def levelNode : Executable.Node:=⟨1,some 0,true,7,[(0,7)]⟩
def highNode : Executable.Node:=⟨2^128,some 1,false,2^140,[(0,2^130)]⟩

private def requireFields (index : Nat) (node parent : Executable.Node) (expected status : Bool) : IO Unit:=do
  let store:=Function.update (parentInput index node parent) 6 [status,false,true]
  unless parentCondition index node parent==expected do
    throw (IO.userError "Parent semantic expectation mismatch")
  match PairTests.runUntil parentFieldsRoutine.program 1000000 ⟨0,store⟩ with
  | none=>throw (IO.userError "Parent field checker did not halt")
  | some (steps,result)=>
    let final:=Function.update store 6 [status && expected,false,true]
    unless (List.finRange 11).all (fun r=>result.store r==final r) do
      throw (IO.userError "Parent field checker violated whole-store semantics")
    unless steps==parentFieldsCost store do
      throw (IO.userError "Parent field checker violated exact cost")
    IO.println s!"Parent field semantics: {steps} stack steps; accepted {status && expected}."

private def requireIndex (code budget : Nat) : IO Unit:=do
  let w : CountWorkspace 0:=Function.Embedding.refl _
  let store : Fin 11→List Bool:=fun r=>if r=0 then Encoding.natural.encode code
    else if r=10 then List.replicate budget false else if r=6 then [true,false] else []
  match PairTests.runUntil (parentIndexRoutine 0 w).program 1000000 ⟨0,store⟩ with
  | none=>throw (IO.userError "Bounded parent conversion did not halt")
  | some (steps,result)=>
    let expected:=parentIndexStore 0 w store code
    unless (List.finRange 11).all (fun r=>result.store r==expected r) do
      throw (IO.userError "Bounded parent conversion violated whole-store semantics")
    unless steps≤64*(budget+(Encoding.natural.encode code).length+1)^3+2 do
      throw (IO.userError "Bounded parent conversion exceeded proved cost")

private def requireLookup (values : List Executable.Node) (parent : Fin values.length)
    (index : Nat) (node : Executable.Node) (status : Bool) : IO Unit:=do
  let store : Fin 28→List Bool:=fun r=>
    if r=17 then Encoding.sequence Encoding.node values++[true,false]
    else if r=18 then List.replicate parent.val false
    else if r=21 then node.level.bits else if r=22 then (parentCode node).bits
    else if r=23 then [node.leader] else if r=24 then index.bits
    else if r=1 then [status,true,false] else if r=27 then [true,false,true] else []
  match PairTests.runUntil parentLookup.program 1000000 ⟨0,store⟩ with
  | none=>throw (IO.userError "Serialized parent lookup did not halt")
  | some (steps,result)=>
    let expected:=Function.update (lookupStore store values[parent]) 1
      [status && parentCondition index node values[parent],true,false]
    unless (List.finRange 28).all (fun r=>result.store r==expected r) do
      throw (IO.userError "Serialized parent lookup violated whole-store semantics")
    IO.println s!"Serialized parent semantic lookup: {steps} stack steps."

def tests : IO Unit:=do
  requireFields 1 levelNode initialNode true true
  requireFields 1 levelNode initialNode true false
  requireFields 0 levelNode initialNode false true
  requireFields 1 {levelNode with parent:=none} initialNode false true
  requireFields 1 {levelNode with level:=3} initialNode false true
  requireFields 1 {levelNode with leader:=false} initialNode false true
  requireFields 3 {highNode with level:=2^128+1,parent:=some 1} highNode true true
  requireFields 3 {highNode with level:=2^128+2,parent:=some 1} highNode false true
  for (code,budget) in [(0,0),(0,3),(1,3),(3,3),(4,3),(2^128,3)] do
    requireIndex code budget
  let values:=[initialNode,levelNode,highNode]
  requireLookup values ⟨0,by decide⟩ 1 levelNode true
  requireLookup values ⟨1,by decide⟩ 2 {levelNode with level:=2,parent:=some 1} true
  requireLookup values ⟨2,by decide⟩ 3 {highNode with level:=2^128+1,parent:=some 2} true
  requireLookup values ⟨0,by decide⟩ 1 {levelNode with leader:=false} true
  requireLookup values ⟨0,by decide⟩ 1 levelNode false
  IO.println "DAG parent semantics passed 8 field, 6 bounded-index and 5 serialized-lookup cases."

#eval tests
end Counting.StackMachine.DagValidation.Tests
