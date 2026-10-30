import Counting.StackRealizabilitySupplyPrefix
import Counting.StackMachineTestLazy

namespace Counting.StackMachine.RealizabilityCheck.SupplyTests
open Routine

private def requireSupply (nodes : List Executable.Node) (values : List Nat)
    (round old total : Nat) (accepted : Bool) : IO Unit:=do
  unless nodes.length==values.length do throw (IO.userError "Supply scan test has unequal input lengths")
  let nodeSuffix:=[true,false,true]
  let weightSuffix:=[false,true,false]
  let store : Store 28:=fun r=>
    if r=17 then (Encoding.list Encoding.node).encode nodes++nodeSuffix
    else if r=20 then (Encoding.list Encoding.natural).encode values++weightSuffix
    else if r=1 then accepted::[false,true]
    else if r=26 then total.bits else if r=22 then (round+1).bits else if r=25 then (old+1).bits else []
  let vista:Executable.Vista:=⟨nodes.toArray,0⟩
  let count:=RealizabilityVerifier.supply vista values.toArray round old
  let program:=supplyPrefix.program
  match TestLazy.finishWithin program 10000000 0 (TestLazy.empty program) ⟨0,store⟩ with
  | none=>throw (IO.userError "Supply scan exceeded test fuel")
  | some (steps,result)=>
    let final:=supplyPrefixStore store nodes values (round+1) old total nodeSuffix weightSuffix
    unless (List.finRange 30).all (fun r=>result.store r==final r) do
      throw (IO.userError "Supply scan violated its full-store contract")
    unless result.store 26==(total+count).bits && result.store 1==(accepted::[false,true]) do
      throw (IO.userError "Supply scan disagrees with actual verifier supply")
    unless steps≤1700000*((store 17).length+(store 20).length+total.size+(round+1).size+(old+1).size+1)^9 do
      throw (IO.userError "Supply scan exceeded proved polynomial")
    IO.println s!"Supply: {nodes.length} stored nodes, {steps} stack instructions; exact count {count}."

def tests : IO Unit:=do
  let root:Executable.Node:=⟨0,none,true,0,[]⟩
  let a:Executable.Node:=⟨1,some 0,true,1,[(0,3)]⟩
  let b:Executable.Node:=⟨1,some 1,false,2,[(0,1)]⟩
  let c:Executable.Node:=⟨2,some 0,true,1,[]⟩
  requireSupply [] [] 0 0 8 true
  requireSupply [root] [8] 0 0 0 true
  requireSupply [root,a] [8,5] 0 0 0 true
  requireSupply [root,a,a,b,c] [8,2,3,7,11] 0 0 4 true
  requireSupply [root,a,a,b,c] [8,2,3,7,11] 0 1 4 true
  requireSupply [root,a,a,b,c] [8,2,3,7,11] 1 0 4 true
  requireSupply [root,a,b] [8,0,2] 0 0 0 false
  requireSupply [a,b] [2^128,2^128+1] 0 0 (2^128) true
  requireSupply [a,b] [2,3] 0 (2^128) 7 true
  requireSupply [{a with level:=2^128}] [2^128] (2^128-1) 0 0 true
  requireSupply [{a with degree:=2^64}] [2^64+1] 0 0 7 true
  requireSupply [{a with degree:=0}] [2^128] 0 0 8 true
  IO.println "Supply scan passed 12 full-store cases against the actual verifier, including zero and 65-bit degrees."

#eval tests
end Counting.StackMachine.RealizabilityCheck.SupplyTests
