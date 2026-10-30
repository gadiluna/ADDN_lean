import Counting.StackEncodingDagMachine
import Counting.StackEncodingPairTests

namespace Counting.StackMachine.EncodingPrograms.DagParser.Tests

def initialNode : Executable.Node := ⟨0,none,true,0,[]⟩
def innerNode : Executable.Node := ⟨1,some 0,false,3,[(0,2),(1,1)]⟩
def hugeNode : Executable.Node := ⟨2,some 1,true,2^128,[(0,2^128),(1,0)]⟩
def emptyVista : Executable.Vista := ⟨#[],0⟩
def oneVista : Executable.Vista := ⟨#[initialNode],0⟩
def nestedVista : Executable.Vista := ⟨#[initialNode,innerNode,hugeNode],2⟩

def start (input : List Bool) : Fin 17 → List Bool :=
  fun r => if r=0 then input else if r=1 then [true,false] else if r=2 then [false,true] else []

private def requirePrefix (value : Executable.Vista) (suffix : List Bool) : IO Unit := do
  let encoded:=Encoding.vista.encode value
  let input:=encoded++suffix
  match PairTests.runUntil vista.routine.program 1000000 ⟨0,start input⟩ with
  | none => throw (IO.userError "DAG parser did not halt within stack test budget")
  | some (steps,result) =>
    let expected : Fin 17 → List Bool := fun r =>
      if r=0 then suffix else if r=1 then [true,false]
      else if r=2 then encoded.reverse++[false,true] else []
    unless (List.finRange 17).all (fun r => result.store r == expected r) do
      throw (IO.userError "DAG parser did not preserve the full register contract")
    unless steps ≤ 3890*(input.length+1)^4 do throw (IO.userError "DAG parser exceeds stack bound")
    IO.println s!"DAG canonical prefix: {steps} stack steps, all scratch restored."

private def requireExact (input : List Bool) (accepted : Bool) : IO Unit := do
  match PairTests.runUntil vistaRecognitionProgram 1000000 (initial vistaRecognitionProgram input) with
  | none => throw (IO.userError "Exact DAG parser did not halt within stack test budget")
  | some (steps,result) =>
    unless result.store 1 == [accepted] do throw (IO.userError "Exact DAG parser result mismatch")
    unless steps ≤ 3910*(input.length+1)^4 do throw (IO.userError "Exact DAG parser exceeds bound")
    IO.println s!"DAG exact syntax: {steps} stack steps, result {accepted}."

private def requireMachine (input : List Bool) (accepted : Bool) : IO Unit := do
  let machine:=Compiler.compile vistaRecognitionProgram
  match EncodingPrograms.Tests.finishWithin machine 10000000 (Machine.initial machine input) with
  | none => throw (IO.userError "Compiled DAG parser did not halt within physical test budget")
  | some (steps,result) =>
    let right:=result.tape.head::result.tape.right
    unless result.tape.left.all (· == .blank) && right.take 1 == [Machine.bitSymbol accepted] &&
        (right.drop 1).all (· == .blank) do
      throw (IO.userError "Compiled DAG parser has wrong result or dirty final tape")
    unless steps ≤ 308898000*(input.length+1)^10 do throw (IO.userError "Compiled DAG parser exceeds bound")
    IO.println s!"DAG physical syntax: {steps} transitions, clean result {accepted}."

def tests : IO Unit := do
  for value in [emptyVista,oneVista,nestedVista] do
    requirePrefix value []
    requirePrefix value [true,false,true]
  -- Empty node arrays are a valid serialization. Graph validity remains a
  -- separate check: this test deliberately keeps that distinction observable.
  for (input,accepted) in [([],false),([true],false),(Encoding.vista.encode emptyVista,true),
      (Encoding.vista.encode oneVista,true),(Encoding.vista.encode nestedVista,true),
      (Encoding.vista.encode oneVista++[false],false),
      (Encoding.frame [false]++Encoding.natural.encode 0,false),
      (Encoding.natural.encode (2^100)++[false],false),
      (Encoding.natural.encode 1++[false],false)] do
    requireExact input accepted
  for (input,accepted) in [([],false),(Encoding.vista.encode emptyVista,true),
      (Encoding.vista.encode oneVista,true),(Encoding.vista.encode emptyVista++[true],false)] do
    requireMachine input accepted
  IO.println "DAG codecs passed 6 full-store, 9 exact-stack and 4 physical-TM cases."

#eval tests
end Counting.StackMachine.EncodingPrograms.DagParser.Tests
