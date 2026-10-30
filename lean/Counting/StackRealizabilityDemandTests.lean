import Counting.StackRealizabilityDemandPrefix
import Counting.StackMachineTestLazy

namespace Counting.StackMachine.RealizabilityCheck.DemandTests
open Routine

private def requireDemand (nodes : List Executable.Node) (values : List Nat)
    (round old total : Nat) (accepted : Bool) : IO Unit:=do
  unless nodes.length==values.length do throw (IO.userError "Demand scan test has unequal input lengths")
  let nodeSuffix:=[true,false,true]
  let weightSuffix:=[false,true,false]
  let store : Store 30:=fun r=>
    if r=17 then (Encoding.list Encoding.node).encode nodes++nodeSuffix
    else if r=20 then (Encoding.list Encoding.natural).encode values++weightSuffix
    else if r=1 then accepted::[false,true]
    else if r=26 then total.bits else if r=22 then (round+1).bits else if r=25 then old.bits else []
  let vista:Executable.Vista:=⟨nodes.toArray,0⟩
  let count:=RealizabilityVerifier.demand vista values.toArray round old
  let program:=demandPrefix.program
  match TestLazy.finishWithin program 10000000 0 (TestLazy.empty program) ⟨0,store⟩ with
  | none=>throw (IO.userError "Demand scan exceeded test fuel")
  | some (steps,result)=>
    let final:=demandPrefixStore store nodes values (round+1) old total nodeSuffix weightSuffix
    unless (List.finRange 32).all (fun r=>result.store r==final r) do
      throw (IO.userError "Demand scan violated its full-store contract")
    unless result.store 26==(total+count).bits && result.store 1==(accepted::[false,true]) do
      throw (IO.userError "Demand scan disagrees with actual verifier demand")
    unless steps≤93000000*((store 17).length+(store 20).length+total.size+(round+1).size+old.size+1)^15 do
      throw (IO.userError "Demand scan exceeded proved polynomial")
    IO.println s!"Demand: {nodes.length} stored nodes, {steps} stack instructions; exact count {count}."

def tests : IO Unit:=do
  let root:Executable.Node:=⟨0,none,true,0,[]⟩
  let a:Executable.Node:=⟨1,some 0,true,1,[(0,3)]⟩
  let b:Executable.Node:=⟨1,some 1,false,2,[(0,1)]⟩
  let c:Executable.Node:=⟨2,some 0,true,1,[]⟩
  requireDemand [] [] 0 0 8 true
  requireDemand [root] [8] 0 0 0 true
  requireDemand [root,a] [8,5] 0 0 0 true
  requireDemand [root,a,a,b,c] [8,2,3,7,11] 0 0 4 true
  requireDemand [root,a,a,b,c] [8,2,3,7,11] 0 1 4 true
  requireDemand [root,a,a,b,c] [8,2,3,7,11] 1 0 4 true
  requireDemand [root,a,b] [8,0,2] 0 0 0 false
  requireDemand [a,b] [2^128,2^128+1] 0 0 (2^128) true
  requireDemand [a,b] [2,3] 0 (2^128) 7 true
  requireDemand [{a with level:=2^128}] [2^128] (2^128-1) 0 0 true
  requireDemand [{a with incoming:=[(0,2^64)]}] [2^64+1] 0 0 7 true
  requireDemand [{a with incoming:=[]}] [2^128] 0 0 8 true
  requireDemand [{a with incoming:=[(0,3),(2,2^80),(9,7)]}] [2^64+1] 0 2 7 true
  requireDemand [{a with incoming:=[(0,3),(2,2^80),(9,7)]}] [2^64+1] 0 8 7 true
  IO.println "Demand scan passed 14 full-store cases against the actual verifier, including missing sources and 81-bit multiplicities."

#eval tests
end Counting.StackMachine.RealizabilityCheck.DemandTests
