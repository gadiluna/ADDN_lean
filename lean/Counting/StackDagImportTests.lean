import Counting.StackDagImportNodes
import Counting.StackMachineTestLazy

namespace Counting.StackMachine.DagUpdate.Import.Tests

def tests : IO Unit := do
  let program := importNodes.program
  let root : Executable.Node := ⟨0,none,false,0,[]⟩
  let leader : Executable.Node := ⟨0,none,true,0,[]⟩
  let child : Executable.Node := ⟨1,some 0,false,3,[(0,2),(1,1)]⟩
  let reordered : Executable.Node := ⟨2,some 1,false,4,[(1,2),(0,0),(1,3)]⟩
  let huge : Executable.Node := ⟨2^128,some (2^129),true,2^130,[(2^127,2^130)]⟩
  let cases : List (List Executable.Node×List Executable.Node) :=
    [([],[]),([root],[]),([],[root]),([root],[root]),
     ([root],[leader,root]),([],[root,root,child]),
     ([leader,root],[root,leader,child]),([root,leader],[child,reordered]),
     ([],[huge]),([huge],[huge,huge]),([child,child],[child])]
  let suffix := [true,false,true]
  let mut maximum := 0
  for (old,nodes) in cases do
    let pool := old.toArray
    let vista : Executable.Vista := ⟨nodes.toArray,0⟩
    let store : Fin 96→List Bool := fun r=>
      if r=70 then (Encoding.list Encoding.node).encode nodes++suffix
      else if r=64 then (Encoding.array Encoding.node).encode pool
      else if r=71 then [true]
      else if r=69 || 74 ≤ r.val then [false,true]++r.val.bits else []
    let result := Executable.importVista pool vista
    let expected := Function.update (Function.update (Function.update store 70 suffix)
      1 ((Encoding.array Encoding.natural).encode result.2))
      64 ((Encoding.array Encoding.node).encode result.1)
    match TestLazy.finishWithin program 30000000 0 (TestLazy.empty program) ⟨0,store⟩ with
    | none => throw (IO.userError "DAG import exceeded test fuel")
    | some (steps,finish) =>
      unless (List.finRange 96).all (fun r=>finish.store r==expected r) do
        throw (IO.userError "DAG import full-store mismatch")
      maximum := max maximum steps
  IO.println s!"DAG import: {cases.length} full-store tests passed; empty tables, shared nodes, reference collisions, unordered/zero multiplicities, 131-bit labels, suffix and external sentinels; maximum {maximum} instructions."

#eval tests
end Counting.StackMachine.DagUpdate.Import.Tests
