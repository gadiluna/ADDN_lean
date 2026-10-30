import Counting.StackDagInitial
import Counting.StackEncodingPairTests

namespace Counting.StackMachine.DagValidation.InitialTests
open Routine EncodingPrograms

private def requireInitial (node : Executable.Node) (expected status : Bool) : IO Unit:=do
  let store : Store 6:=![node.level.bits,(parentCode node).bits,nodeSuffix node,[status,false,true],[],[],[],[]]
  match PairTests.runUntil initialCheckRoutine.program 100000 ⟨0,store⟩ with
  | none=>throw (IO.userError "Initial node checker did not halt")
  | some (steps,result)=>
    let final:=Function.update store 3 [status && expected,false,true]
    unless initialCheck store==expected && (List.finRange 8).all (fun r=>result.store r==final r) do
      throw (IO.userError "Initial node checker violated independent/full-store expectations")
    unless steps==initialCost store do
      throw (IO.userError "Initial node checker violated exact cost")

def tests : IO Unit:=do
  let node : Executable.Node:=⟨0,none,false,0,[]⟩
  for status in [true,false] do
    requireInitial node true status
    requireInitial {node with leader:=true} true status
    requireInitial {node with level:=1} false status
    requireInitial {node with parent:=some 0} false status
    requireInitial {node with degree:=2^128} false status
    requireInitial {node with incoming:=[(0,1)]} false status
    requireInitial {node with incoming:=[(0,0)]} false status
  IO.println "Initial-node semantic check passed 14 exact-cost full-store cases."

#eval tests
end Counting.StackMachine.DagValidation.InitialTests
