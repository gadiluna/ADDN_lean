import Counting.StackRealizabilityInitialChecked
import Counting.StackDagTestRun

namespace Counting.StackMachine.RealizabilityCheck.InitialCheckedTests
open Routine

private def requireInitial (nodes : List Executable.Node) (values : List Nat)
    (ell order : Nat) (accepted expected : Bool) : IO Unit:=do
  unless nodes.length==values.length do throw (IO.userError "Initial-check test has unequal input lengths")
  let nodeSuffix:=[true,false,true]
  let weightSuffix:=[false,true,false]
  let store : Store 26:=fun r=>
    if r=17 then (Encoding.list Encoding.node).encode nodes++nodeSuffix
    else if r=20 then (Encoding.list Encoding.natural).encode values++weightSuffix
    else if r=1 then accepted::[false,true]
    else if r=26 then ell.bits else if r=27 then order.bits else []
  let vista:Executable.Vista:=⟨nodes.toArray,0⟩
  let leaders:=RealizabilityVerifier.initialCount vista values.toArray true
  let nonleaders:=RealizabilityVerifier.initialCount vista values.toArray false
  unless initialBoundsCheck leaders nonleaders ell order==expected do
    throw (IO.userError "Incorrect expected initial-check specification")
  match DagValidation.TestRun.run initialCheck.program 10000000 0 ⟨0,store⟩ with
  | none=>throw (IO.userError "Initial capacity check exceeded test fuel")
  | some (steps,result)=>
    let final:=initialCheckStore store accepted [false,true] nodes values ell order nodeSuffix weightSuffix
    unless (List.finRange 28).all (fun r=>result.store r==final r) do
      throw (IO.userError "Initial capacity check violated its full-store contract")
    unless result.store 1==((accepted&&expected)::[false,true]) do
      throw (IO.userError "Initial capacity check disagrees with actual verifier component")
    unless steps≤13200*((store 17).length+(store 20).length+ell.size+order.size+1)^5 do
      throw (IO.userError "Initial capacity check exceeded proved polynomial")
    IO.println s!"Initial verifier component: {steps} stack instructions; exact result {expected}."

def tests : IO Unit:=do
  let leader:Executable.Node:=⟨0,none,true,0,[]⟩
  let other:Executable.Node:=⟨0,none,false,0,[]⟩
  let child:Executable.Node:=⟨1,some 0,true,1,[(1,3)]⟩
  requireInitial [] [] 0 0 true false
  requireInitial [] [] 1 1 true true
  requireInitial [leader] [1] 1 1 true true
  requireInitial [leader] [2] 1 2 true false
  requireInitial [leader,other,child] [2,3,1] 2 5 true true
  requireInitial [leader,other,child] [2,3,1] 2 4 true false
  requireInitial [leader,other,child] [2,3,1] 1 5 true false
  requireInitial [leader,other] [0,0] 2 1 true false
  requireInitial [leader,other] [2,3] 2 5 false true
  requireInitial [leader,other,child] [2^128,2^128-1,1] (2^128) (2^129-1) true true
  IO.println "Complete initial capacity pass passed 10 full-store cases against the actual verifier sums."

#eval tests
end Counting.StackMachine.RealizabilityCheck.InitialCheckedTests
