import Counting.StackDagReferenceLookup
import Counting.StackMachineTestLazy

namespace Counting.StackMachine.DagUpdate.ReferenceTests

def roles : ReferenceWorkspace 1 := ⟨fun i=>⟨i.val+1,by omega⟩,by
  intro a b h
  apply Fin.ext
  have eq:=congrArg (fun i : Fin 15=>i.val) h
  dsimp at eq
  omega⟩

def tests : IO Unit := do
  let program:=(referenceLookup 1 roles).program
  let mut maximum:=0
  for values in [[],[0],[9,0,3],[2^129+3,4,2^128],[1,2,3,4,5]] do
    for index in [0,1,values.length,2^128] do
      let store : Fin 15→List Bool:=fun r=>
        if r=roles 0 then (Encoding.list Encoding.natural).encode values
        else if r=roles 1 then Encoding.natural.encode index
        else if r=roles 2 then [false,true,false] else if r=0 then [true,false,true,true] else []
      let expected:=Function.update store (roles 2) ((values[index]?.getD 0).bits++store (roles 2))
      match TestLazy.finishWithin program 20000000 0 (TestLazy.empty program) ⟨0,store⟩ with
      | none=>throw (IO.userError s!"binary mapping access exceeded test fuel: length={values.length}, index={index}")
      | some (steps,finish)=>
        unless (List.finRange 15).all (fun r=>finish.store r==expected r) do
          throw (IO.userError "binary mapping access full-store mismatch")
        maximum:=max maximum steps
  IO.println s!"DAG binary mapping lookup: 20 full-store tests passed; empty/out-of-range/129-bit index, 130-bit values and external/output sentinels; maximum {maximum} instructions."

#eval tests
end Counting.StackMachine.DagUpdate.ReferenceTests
