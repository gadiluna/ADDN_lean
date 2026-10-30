import Counting.HardnessNetworkMachineSerialize
import Counting.StackMachineTestLazy

namespace Counting.HardnessNetworkMachine.SerializeTests
open StackMachine
private def workspace : SerializeWorkspace 2 :=
  ⟨fun i=>⟨i.val,by omega⟩,by intro a b h;exact Fin.ext (congrArg (fun i : Fin 11=>i.val) h)⟩
def tests : IO Unit := do
  let program:=(emitNetworkSerialization 2 workspace).program
  let mut count:=0
  let mut maximum:=0
  for base in [1,3,5] do
    for values in [[],[0],[1,2],[37,2^128+1,11]] do
      let width:=networkOrder base values
      let store : Fin 11→List Bool:=fun r=>
        if r=0 then List.replicate width false else if r=1 then List.replicate base false
        else if r=2 then ((Encoding.list (Encoding.list Encoding.natural)).encode (pathMatrix base values)).reverse
        else if r=3 then ((Encoding.list (Encoding.list Encoding.natural)).encode (starMatrix base values)).reverse
        else if r=4 then [true,false] else if r=9 then [false,true,true] else if r=10 then [true,false,true] else []
      let expected:=Function.update store 4 ((networkWord base values).reverse++store 4)
      match TestLazy.finishWithin program 10000000 0 (TestLazy.empty program) ⟨0,store⟩ with
      | none=>throw (IO.userError "network serialization exceeded fuel")
      | some (steps,finish)=>
        unless (List.finRange 11).all (fun r=>finish.store r==expected r) do
          throw (IO.userError "network serialization full-store mismatch")
        count:=count+1;maximum:=max maximum steps
  IO.println s!"Hardness network serializer: {count} full-store cases passed; markers/round headers, base1, cached matrices repeated, 129-bit coefficients, sentinels; maximum {maximum} stack transitions."
#eval tests
end Counting.HardnessNetworkMachine.SerializeTests
