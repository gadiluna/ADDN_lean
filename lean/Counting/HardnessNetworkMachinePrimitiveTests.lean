import Counting.HardnessNetworkMachineRows
import Counting.HardnessNetworkMachineLeaderBlock
import Counting.StackMachineTestLazy

namespace Counting.HardnessNetworkMachine.PrimitiveTests
open StackMachine
private def rows : RowsWorkspace 2 :=
  ⟨fun i=>⟨i.val,by omega⟩,by intro a b h;exact Fin.ext (congrArg (fun i : Fin 12=>i.val) h)⟩
private def leader : LeaderWorkspace 2 :=
  ⟨fun i=>⟨i.val,by omega⟩,by intro a b h;exact Fin.ext (congrArg (fun i : Fin 42=>i.val) h)⟩
def tests : IO Unit := do
  let single:=(emitOneHotRow 3 rows.row).program
  let consecutive:=(emitConsecutiveRows 2 rows).program
  let blocks:=(emitLeaderBlock 2 leader).program
  let mut count:=0
  let mut maximum:=0
  for width in [1,2,5,11] do
    for target in (List.range width) do
      let store : Fin 12→List Bool:=fun r=>
        if r=0 then List.replicate width false else if r=1 then List.replicate target true
        else if r=2 then [false,true] else if r=10 then [true,false,true] else if r=11 then [true,true] else []
      let expected:=Function.update store 2 (((Encoding.list Encoding.natural).encode (oneHotRow width target)).reverse++store 2)
      match TestLazy.finishWithin single 2000000 0 (TestLazy.empty single) ⟨0,store⟩ with
      | none=>throw (IO.userError "network one-hot row exceeded fuel")
      | some (steps,finish)=>
        unless (List.finRange 12).all (fun r=>finish.store r==expected r) do
          throw (IO.userError "network one-hot row full-store mismatch")
        count:=count+1; maximum:=max maximum steps
  for (width,start,amount) in [(1,0,0),(1,0,1),(5,0,5),(5,2,3),(11,1,7)] do
    let store : Fin 12→List Bool:=fun r=>
      if r=0 then List.replicate width false else if r=1 then List.replicate start false
      else if r=2 then [false,true] else if r=9 then List.replicate amount true
      else if r=10 then [true,false,true] else if r=11 then [true,true] else []
    let expected:=consecutiveRowsResult rows store amount
    match TestLazy.finishWithin consecutive 2000000 0 (TestLazy.empty consecutive) ⟨0,store⟩ with
    | none=>throw (IO.userError "network path rows exceeded fuel")
    | some (steps,finish)=>
      unless (List.finRange 12).all (fun r=>finish.store r==expected r) do
        throw (IO.userError "network path rows full-store mismatch")
      count:=count+1; maximum:=max maximum steps
  for value in [0,1,37,2^128+1] do
    for amount in [0,1,4] do
      let suffix:=[false,true,false]
      let store : Fin 42→List Bool:=fun r=>
        if r=0 then Encoding.natural.encode value++suffix else if r=1 then [false,true]
        else if r=33 then List.replicate amount false else if r=35 then [true,false]
        else if r=40 then [false,true,true] else if r=41 then [true,false,true] else []
      let expected:=Function.update (Function.update store 0 suffix) 35
        ((Encoding.sequence Encoding.natural (List.replicate amount value)).reverse++store 35)
      match TestLazy.finishWithin blocks 2000000 0 (TestLazy.empty blocks) ⟨0,store⟩ with
      | none=>throw (IO.userError "network leader block exceeded fuel")
      | some (steps,finish)=>
        unless (List.finRange 42).all (fun r=>finish.store r==expected r) do
          throw (IO.userError "network leader block full-store mismatch")
        count:=count+1; maximum:=max maximum steps
  IO.println s!"Hardness network primitives: {count} full-store cases passed; boundary columns, empty blocks, 129-bit coefficients, suffix/status/sentinels preserved; maximum {maximum} stack transitions."
#eval tests
end Counting.HardnessNetworkMachine.PrimitiveTests
