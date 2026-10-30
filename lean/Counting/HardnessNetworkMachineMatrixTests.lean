import Counting.HardnessNetworkMachinePath
import Counting.HardnessNetworkMachineStar
import Counting.StackMachineTestLazy

namespace Counting.HardnessNetworkMachine.MatrixTests
open StackMachine
private def matrix : MatrixWorkspace 2 :=
  ⟨fun i=>⟨i.val,by omega⟩,by intro a b h;exact Fin.ext (congrArg (fun i : Fin 18=>i.val) h)⟩
def tests : IO Unit := do
  let paths:=(emitPathMatrix 2 matrix).program
  let stars:=(emitStarMatrix 2 matrix).program
  let mut count:=0
  let mut maximum:=0
  for base in [1,3,5] do
    for values in [[0],[1,2],[37,2^128+1,11]] do
      let width:=networkOrder base values
      let store : Fin 18→List Bool:=fun r=>
        if r=0 then List.replicate width false else if r=2 then [true,false]
        else if r=10 then List.replicate base true else if r=15 then List.replicate values.tail.length true
        else if r=13 then ((Encoding.list Encoding.natural).encode (leaderRow base values)).reverse
        else if r=16 then [false,true,true] else if r=17 then [true,false,true] else []
      let pathExpected:=Function.update store 2
        (((Encoding.list (Encoding.list Encoding.natural)).encode (pathMatrix base values)).reverse++store 2)
      match TestLazy.finishWithin paths 10000000 0 (TestLazy.empty paths) ⟨0,store⟩ with
      | none=>throw (IO.userError "network path matrix exceeded fuel")
      | some (steps,finish)=>
        unless (List.finRange 18).all (fun r=>finish.store r==pathExpected r) do
          throw (IO.userError "network path matrix full-store mismatch")
        count:=count+1;maximum:=max maximum steps
      let starExpected:=Function.update store 2
        (((Encoding.list (Encoding.list Encoding.natural)).encode (starMatrix base values)).reverse++store 2)
      match TestLazy.finishWithin stars 10000000 0 (TestLazy.empty stars) ⟨0,store⟩ with
      | none=>throw (IO.userError "network star matrix exceeded fuel")
      | some (steps,finish)=>
        unless (List.finRange 18).all (fun r=>finish.store r==starExpected r) do
          throw (IO.userError "network star matrix full-store mismatch")
        count:=count+1;maximum:=max maximum steps
  IO.println s!"Hardness network matrices: {count} full-store cases passed; actual path/star matrices, empty ordinary family, base1, 129-bit multiplicities, sentinels; maximum {maximum} stack transitions."
#eval tests
end Counting.HardnessNetworkMachine.MatrixTests
