import Counting.StackRealizabilityInitialPrefix
import Counting.StackDagTestRun

namespace Counting.StackMachine.RealizabilityCheck.InitialTests
open Routine

private def requireInitial (nodes : List Executable.Node) (values : List Nat)
    (leaders nonleaders : Nat) (accepted : Bool) : IO Unit:=do
  unless nodes.length==values.length do throw (IO.userError "Initial-sum test has unequal input lengths")
  let nodeSuffix:=[true,false,true]
  let weightSuffix:=[false,true,false]
  let store : Store 24:=fun r=>
    if r=17 then (Encoding.list Encoding.node).encode nodes++nodeSuffix
    else if r=20 then (Encoding.list Encoding.natural).encode values++weightSuffix
    else if r=1 then accepted::[false,true]
    else if r=21 then leaders.bits else if r=22 then nonleaders.bits else []
  let vista:Executable.Vista:=⟨nodes.toArray,0⟩
  let first:=RealizabilityVerifier.initialCount vista values.toArray true
  let second:=RealizabilityVerifier.initialCount vista values.toArray false
  match DagValidation.TestRun.run initialPrefix.program 10000000 0 ⟨0,store⟩ with
  | none=>throw (IO.userError "Initial count scan exceeded test fuel")
  | some (steps,result)=>
    let expected:=initialPrefixStore store nodes values leaders nonleaders nodeSuffix weightSuffix
    unless (List.finRange 26).all (fun r=>result.store r==expected r) do
      throw (IO.userError "Initial count scan violated its full-store contract")
    unless result.store 21==(leaders+first).bits && result.store 22==(nonleaders+second).bits &&
        result.store 1==accepted::[false,true] do
      throw (IO.userError "Initial count scan disagrees with actual verifier initialCount")
    unless steps≤13000*((store 17).length+(store 20).length+leaders.size+nonleaders.size+1)^5 do
      throw (IO.userError "Initial count scan exceeded proved polynomial")
    IO.println s!"Initial counts: {nodes.length} stored nodes, {steps} stack instructions; sums agree with verifier."

def tests : IO Unit:=do
  let leader:Executable.Node:=⟨0,none,true,0,[]⟩
  let other:Executable.Node:=⟨0,none,false,0,[]⟩
  let child:Executable.Node:=⟨1,some 0,true,1,[(1,3)]⟩
  requireInitial [] [] 5 8 true
  requireInitial [leader] [3] 0 0 true
  requireInitial [other] [5] 0 0 true
  requireInitial [leader,other,child] [2,3,1] 0 0 true
  requireInitial [leader,child,other] [2,100,3] 4 5 true
  requireInitial [leader,leader] [2,3] 0 0 true
  requireInitial [leader,other,child] [2^128,2^128+1,1] (2^128) 7 true
  requireInitial [leader,other] [2,3] 7 9 false
  requireInitial [leader,other] [0,0] 7 9 true
  requireInitial [leader,{child with level:=2^128}] [4,2^128] 0 0 true
  IO.println "Initial leader/nonleader sums passed 10 full-store cases; graph validity and positivity remain separate checks."

#eval tests
end Counting.StackMachine.RealizabilityCheck.InitialTests
