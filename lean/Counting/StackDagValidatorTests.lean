import Counting.StackDagValidatorSyntax
import Counting.StackDagTestRun
import Counting.MachineFramedCompareTests

namespace Counting.StackMachine.DagValidation.ValidatorTests
open Routine EncodingPrograms

private def requireStack (name : String) (input : List Bool) (expected : Bool) : IO Unit:=do
  unless validWord input==expected do
    throw (IO.userError s!"DAG validator reference expectation mismatch: {name}")
  match TestRun.run validationProgram 10000000 0 (initial validationProgram input) with
  | none=>throw (IO.userError s!"DAG validator failed to halt within test budget: {name}")
  | some (steps,result)=>
    unless (List.finRange 37).all (fun r=>result.store r==outputStore 35 [expected] r) do
      throw (IO.userError s!"DAG validator violated full-store result: {name}")
    unless steps≤225000000*(input.length+1)^6 do
      throw (IO.userError s!"DAG validator exceeded proved bound: {name}")
    IO.println s!"Complete DAG validation {name}: {steps} stack instructions, result {expected}."

private def requireVista (name : String) (nodes : List Executable.Node) (bottom : Nat) (expected : Bool) : IO Unit:=
  requireStack name (Encoding.vista.encode ⟨nodes.toArray,bottom⟩) expected

private def requireMachine (name : String) (input : List Bool) (expected : Bool) : IO Unit:=do
  let machine:=Compiler.compile validationProgram
  match Compare.Framed.Tests.finishWithin machine 30000000 0 (Machine.initial machine input) with
  | none=>throw (IO.userError s!"Compiled DAG validator exceeded physical test fuel: {name}")
  | some (steps,result)=>
    let right:=result.tape.head::result.tape.right
    unless result.tape.left.all (· == .blank) && right.take 1 == [Machine.bitSymbol expected] &&
        (right.drop 1).all (· == .blank) do
      throw (IO.userError s!"Compiled DAG validator has incorrect result or dirty tape: {name}")
    unless steps≤(20*(225000040)^2)*(input.length+1)^14 do
      throw (IO.userError s!"Compiled DAG validator exceeded proved polynomial: {name}")
    IO.println s!"Complete DAG validation {name}: {steps} physical transitions, clean result {expected}."

def tests : IO Unit:=do
  let a:Executable.Node:=⟨0,none,true,0,[]⟩
  let b:Executable.Node:=⟨0,none,false,0,[]⟩
  let child:Executable.Node:=⟨1,some 0,true,0,[]⟩
  let red:Executable.Node:=⟨1,some 0,true,7,[(1,2^128)]⟩
  requireVista "empty table" [] 0 false
  requireVista "singleton" [a] 0 true
  requireVista "two initial states unconnected" [a,b] 1 false
  requireVista "duplicate initial state" [a,a] 1 false
  requireVista "initial degree nonzero" [{a with degree:=1}] 0 false
  requireVista "parent only" [a,child] 1 true
  requireVista "huge red multiplicity" [a,b,red] 2 true
  requireVista "wrong parent leader" [a,{child with leader:=false}] 1 false
  requireVista "wrong parent level" [a,{child with level:=2}] 1 false
  requireVista "forward parent" [a,{child with parent:=some 1}] 1 false
  requireVista "missing visible node" [a,b,child] 2 false
  requireVista "duplicate positive signature" [a,child,child] 2 false
  requireVista "zero red count" [a,{child with incoming:=[(0,0)]}] 1 false
  requireVista "repeated red source" [a,{child with incoming:=[(0,1),(0,2)]}] 1 false
  requireVista "wrong bottom" [a,child] 0 false
  requireVista "huge bottom index" [a] (2^128) false
  for (name,input) in [
      ("empty word",[]),("truncated frame",[true]),
      ("trailing data",Encoding.vista.encode ⟨#[a],0⟩++[false]),
      ("noncanonical count",Encoding.frame [false]++Encoding.natural.encode 0),
      ("huge missing table",Encoding.natural.encode (2^128)++[false])] do
    requireStack name input false
  requireMachine "malformed" [] false
  requireMachine "empty table" (Encoding.vista.encode ⟨#[],0⟩) false
  requireMachine "singleton" (Encoding.vista.encode ⟨#[a],0⟩) true
  IO.println "Complete DAG validator passed 21 full-store stack and 3 physical-TM cases."

#eval tests
end Counting.StackMachine.DagValidation.ValidatorTests
