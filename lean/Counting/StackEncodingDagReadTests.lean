import Counting.StackEncodingDagReadMachine
import Counting.StackEncodingDagTests

namespace Counting.StackMachine.EncodingPrograms.DagParser.ReadTests

def values : List Executable.Node := [Tests.initialNode,Tests.innerNode,Tests.hugeNode]

private def requireRead (input index : List Bool) (status : Bool) (expectedAccepted : Bool)
    (expectedCode : Option (List Bool) := none) : IO Unit := do
  let sentinel:=[true,false,true,false]
  let start : Fin 17→List Bool := fun r =>
    if r=0 then input else if r=1 then [status,true,false] else if r=8 then index
    else if r=10 then sentinel else []
  let effect:=nodeReadEffect index.length input
  unless effect.accepted == expectedAccepted do
    throw (IO.userError "Structured access acceptance differs from independent test expectation")
  match expectedCode with
  | some code => unless effect.code == code do
      throw (IO.userError "Structured access selected the wrong canonical node")
  | none => pure ()
  match PairTests.runUntil nodeRead.program 2000000 ⟨0,start⟩ with
  | none => throw (IO.userError "Structured access exceeded stack test budget")
  | some (steps,result) =>
    let expected:=parseStore 0 1 2 (Function.update start 8 []) status [true,false] effect
    unless (List.finRange 17).all (fun r => result.store r == expected r) do
      throw (IO.userError "Structured access violated its complete register contract")
    unless steps ≤ (2*index.length+1)*2029*(input.length+1)^3+2*index.length+4 do
      throw (IO.userError "Structured access exceeded proved step bound")
    IO.println s!"Structured node access: {steps} stack steps, status {status && effect.accepted}."

private def requireMachine (input expected : List Bool) : IO Unit := do
  unless nodeReadOutput input == expected do throw (IO.userError "Node access output expectation mismatch")
  let machine:=Compiler.compile nodeReadMachineProgram
  match EncodingPrograms.Tests.finishWithin machine 10000000 (Machine.initial machine input) with
  | none => throw (IO.userError "Node access physical machine exceeded test budget")
  | some (steps,result) =>
    let right:=result.tape.head::result.tape.right
    unless result.tape.left.all (· == .blank) &&
        right.take expected.length == expected.map Machine.bitSymbol &&
        (right.drop expected.length).all (· == .blank) do
      throw (IO.userError "Node access physical machine produced wrong output or a dirty tape")
    unless steps ≤ 749088000*(input.length+1)^10 do
      throw (IO.userError "Node access physical machine exceeded proved bound")
    IO.println s!"Structured node access physical machine: {steps} transitions, clean output."

def tests : IO Unit := do
  let code:=Encoding.sequence Encoding.node values
  for index in List.finRange values.length do
    requireRead code (List.replicate index.val true) true true (some (Encoding.node.encode values[index]))
    requireRead (code++[false,true,false]) (List.replicate index.val false) false true
      (some (Encoding.node.encode values[index]))
  for (input,index) in [([],[]),([true],[]),(code,[true,true,true]),
      (Encoding.node.encode Tests.initialNode++[true],[false]),
      (Encoding.natural.encode (2^100),[])] do
    requireRead input index true false
  -- Access validates only the prefix through the selected node.
  requireRead (Encoding.node.encode Tests.initialNode++[true]) [] true true
    (some (Encoding.node.encode Tests.initialNode))
  requireMachine (Encoding.frame []++Encoding.node.encode Tests.initialNode)
    (Encoding.node.encode Tests.initialNode++[true])
  requireMachine (Encoding.frame [false]++Encoding.node.encode Tests.initialNode++
    Encoding.node.encode Tests.innerNode++[true]) (Encoding.node.encode Tests.innerNode++[true])
  requireMachine [] (nodeReadOutput [])
  requireMachine (Encoding.frame [true]++Encoding.node.encode Tests.initialNode)
    (nodeReadOutput (Encoding.frame [true]++Encoding.node.encode Tests.initialNode))
  IO.println "Structured node access passed 12 full-store and 4 physical-TM cases."

#eval tests
end Counting.StackMachine.EncodingPrograms.DagParser.ReadTests
