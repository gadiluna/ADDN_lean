import Counting.HardnessNetworkMachineLeader
import Counting.HardnessNetworkMachineGroup
import Counting.StackMachineTestLazy

namespace Counting.HardnessNetworkMachine.BlockTests
open StackMachine
private def leader : LeaderWorkspace 2 :=
  ⟨fun i=>⟨i.val,by omega⟩,by intro a b h;exact Fin.ext (congrArg (fun i : Fin 42=>i.val) h)⟩
private def group : GroupWorkspace 2 :=
  ⟨fun i=>⟨i.val,by omega⟩,by intro a b h;exact Fin.ext (congrArg (fun i : Fin 14=>i.val) h)⟩
def tests : IO Unit := do
  let leaders:=(emitLeaderRow 2 leader).program
  let groups:=(emitGroup 2 group).program
  let mut count:=0
  let mut maximum:=0
  for base in [1,3,5] do
    for values in [[0],[1,2],[37,2^128+1,11]] do
      let width:=networkOrder base values
      let suffix:=[false,true,false]
      let store : Fin 42→List Bool:=fun r=>
        if r=0 then (Encoding.list Encoding.natural).encode values++suffix else if r=1 then [false,true]
        else if r=32 then List.replicate width false else if r=33 then List.replicate base false
        else if r=35 then [true,false] else if r=40 then [false,true,true] else if r=41 then [true,false,true] else []
      let expected:=Function.update (Function.update store 0 suffix) 35
        (((Encoding.list Encoding.natural).encode (leaderRow base values)).reverse++store 35)
      match TestLazy.finishWithin leaders 5000000 0 (TestLazy.empty leaders) ⟨0,store⟩ with
      | none=>throw (IO.userError "network whole leader row exceeded fuel")
      | some (steps,finish)=>
        unless (List.finRange 42).all (fun r=>finish.store r==expected r) do
          throw (IO.userError "network whole leader row full-store mismatch")
        count:=count+1;maximum:=max maximum steps
  for (width,start,size) in [(1,0,1),(5,1,4),(7,1,3),(11,4,5),(16,1,6),(16,7,5)] do
    let store : Fin 14→List Bool:=fun r=>
      if r=0 then List.replicate width false else if r=1 then List.replicate (start+1) false
      else if r=2 then [true,false] else if r=10 then List.replicate size true
      else if r=12 then [false,true,true] else if r=13 then [true,false,true] else []
    let expected:=groupResult group store start size
    match TestLazy.finishWithin groups 5000000 0 (TestLazy.empty groups) ⟨0,store⟩ with
    | none=>throw (IO.userError "network complete path group exceeded fuel")
    | some (steps,finish)=>
      unless (List.finRange 14).all (fun r=>finish.store r==expected r) do
        throw (IO.userError "network complete path group full-store mismatch")
      count:=count+1;maximum:=max maximum steps
  IO.println s!"Hardness network blocks: {count} full-store cases passed; whole leader rows, complete path groups, 129-bit multiplicity, suffix/status/sentinels; maximum {maximum} stack transitions."
#eval tests
end Counting.HardnessNetworkMachine.BlockTests
