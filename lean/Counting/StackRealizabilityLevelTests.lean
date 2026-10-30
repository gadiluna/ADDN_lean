import Counting.StackRealizabilityLevelPrefix
import Counting.StackDagTestRun

namespace Counting.StackMachine.RealizabilityCheck.LevelTests
open Routine

private def requireLevel (nodes : List Executable.Node) (values : List Nat)
    (round total N : Nat) (accepted : Bool) : IO Unit:=do
  unless nodes.length==values.length do throw (IO.userError "Level scan test has unequal input lengths")
  let nodeSuffix:=[true,false,true]
  let weightSuffix:=[false,true,false]
  let store : Store 25:=fun r=>
    if r=17 then (Encoding.list Encoding.node).encode nodes++nodeSuffix
    else if r=20 then (Encoding.list Encoding.natural).encode values++weightSuffix
    else if r=1 then accepted::[false,true]
    else if r=21 then total.bits else if r=22 then (round+1).bits else []
  let vista:Executable.Vista:=⟨nodes.toArray,0⟩
  let count:=((Executable.levelNodes vista (round+1)).map (RealizabilityVerifier.weight values.toArray)).sum
  match DagValidation.TestRun.run levelPrefix.program 10000000 0 ⟨0,store⟩ with
  | none=>throw (IO.userError "Level count scan exceeded test fuel")
  | some (steps,result)=>
    let final:=levelPrefixStore store nodes values (round+1) total nodeSuffix weightSuffix
    unless (List.finRange 27).all (fun r=>result.store r==final r) do
      throw (IO.userError "Level count scan violated its full-store contract")
    unless result.store 21==(total+count).bits && result.store 1==(accepted::[false,true]) do
      throw (IO.userError "Level count scan disagrees with actual visible mass")
    unless N-count==RealizabilityVerifier.hidden N vista values.toArray round do
      throw (IO.userError "Level count scan disagrees with actual hidden mass")
    unless steps≤13000*((store 17).length+(store 20).length+total.size+(round+1).size+1)^5 do
      throw (IO.userError "Level count scan exceeded proved polynomial")
    IO.println s!"Level count: {nodes.length} stored nodes, {steps} stack instructions; exact count {count}."

def tests : IO Unit:=do
  let root:Executable.Node:=⟨0,none,true,0,[]⟩
  let a:Executable.Node:=⟨1,some 0,true,1,[(0,3)]⟩
  let b:Executable.Node:=⟨1,some 1,false,2,[(0,1)]⟩
  let c:Executable.Node:=⟨2,some 0,true,1,[]⟩
  requireLevel [] [] 0 8 0 true
  requireLevel [root] [8] 0 0 8 true
  requireLevel [root,a] [8,5] 0 0 8 true
  requireLevel [root,a,a,b,c] [8,2,3,7,11] 0 4 20 true
  requireLevel [root,a,a,b,c] [8,2,3,7,11] 0 4 12 true
  requireLevel [root,a,a,b,c] [8,2,3,7,11] 0 4 1 true
  requireLevel [root,a,a,b,c] [8,2,3,7,11] 1 4 11 true
  requireLevel [root,a,b] [8,0,2] 0 0 1 false
  requireLevel [a,b] [2^128,2^128+1] 0 (2^128) (2^129) true
  requireLevel [{a with level:=2^128}] [2^128] (2^128-1) 0 (2^129) true
  IO.println "Level scan passed 10 full-store cases, including hidden mass zero, positive, and truncated at zero."

#eval tests
end Counting.StackMachine.RealizabilityCheck.LevelTests
