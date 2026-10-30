import Counting.StackNaturalPowerBounds
import Counting.StackMachineTestLazy

namespace Counting.StackMachine.NaturalPower.Tests
private def workspace : Workspace 2 :=
  ⟨fun i=>⟨i.val,by omega⟩,by intro a b h;exact Fin.ext (congrArg (fun i : Fin 17=>i.val) h)⟩
def tests : IO Unit := do
  let program := (powerRoutine 2 workspace).program
  let mut maximum:=0
  for base in [0,1,2,5,17] do
    for exponent in [0,1,2,4] do
      let store : Fin 17 → List Bool := fun r=>
        if r=0 then base.bits else if r=13 then List.replicate exponent true
        else if r=15 then [true,false] else if r=16 then [false,true,false] else []
      let expected:=Function.update (Function.update store 13 []) 1 (base^exponent).bits
      match TestLazy.finishWithin program 2000000 0 (TestLazy.empty program) ⟨0,store⟩ with
      | none=>throw (IO.userError "binary power exceeded test fuel")
      | some (steps,finish)=>
        unless (List.finRange 17).all (fun r=>finish.store r==expected r) do
          throw (IO.userError "binary power full-store contract mismatch")
        maximum:=max maximum steps
  IO.println s!"Binary power: 20 full-store cases passed, including 0^0, zero base, zero exponent and sentinel preservation; max {maximum} stack transitions."
#eval tests
end Counting.StackMachine.NaturalPower.Tests
