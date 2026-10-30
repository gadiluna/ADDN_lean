import Counting.HardnessNetworkMachineBuild
import Counting.StackMachineTestLazy

namespace Counting.HardnessNetworkMachine.BuildTests
open StackMachine
def tests : IO Unit := do
  let program:=buildNetwork.program
  let mut maximum:=0
  for (q,values) in [(0,[0]),(1,[1]),(2,[37,9,5]),(0,[2^128+1])] do
    let B:=q+3
    let N:=networkOrder B values
    let leaderCode:=(Encoding.list Encoding.natural).encode (leaderRow B values)
    let pathCode:=(Encoding.list (Encoding.list Encoding.natural)).encode (pathMatrix B values)
    let starCode:=(Encoding.list (Encoding.list Encoding.natural)).encode (starMatrix B values)
    let store : Fin 96→List Bool:=fun r=>
      if r=0 then (Encoding.list Encoding.natural).encode values else if r=1 then [true]
      else if r=25 then List.replicate values.tail.length true else if r=27 then List.replicate q true
      else if r=17 then [false,true] else if r=31 then [true,false,true]
      else if r=51 then [true,true,false] else if r=52 then [false,true,false] else if r=54 then [true,true,true] else []
    let expected:=Function.update (Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update store 0 []) 1 (networkWord B values)) 64 (List.replicate B true)) 65 (List.replicate N true))
      66 leaderCode.reverse) 69 pathCode.reverse) 79 starCode.reverse
    match TestLazy.finishWithin program 30000000 0 (TestLazy.empty program) ⟨0,store⟩ with
    | none=>throw (IO.userError "network builder exceeded fuel")
    | some (steps,finish)=>
      unless (List.finRange 96).all (fun r=>finish.store r==expected r) do
        throw (IO.userError "network builder full-store mismatch")
      maximum:=max maximum steps
  IO.println s!"Hardness network builder: 4 full-store cases passed; real dimensions, leader/path/star construction and serialization, 129-bit multiplicity, reserved registers preserved; maximum {maximum} stack transitions."
#eval tests
end Counting.HardnessNetworkMachine.BuildTests
