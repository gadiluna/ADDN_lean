import Counting.StackEmitTripleSelected
import Counting.StackMachineTestMemo

namespace Counting.StackMachine.Routine.TripleTests

private def workspace : TripleWorkspace 2 := ⟨![6,2,4,1,5,0],by decide⟩

private def checked (selection : Fin 3 → Fin 3) (literals : Fin 3 → Nat×Bool)
    (tail : List Bool) : IO Unit := do
  let source := fun i => literalCodec.encode (literals i)
  let store : Fin 8 → List Bool := ![[],tail,source 1,[true,false],source 2,[],source 0,[false,true,true]]
  let output := ((Encoding.list literalCodec).encode
    [literals (selection 0),literals (selection 1),literals (selection 2)]).reverse++tail
  let expected := Function.update store 1 output
  let cost := 7*((source (selection 0)).length+(source (selection 1)).length+(source (selection 2)).length)+25
  let program := TestRun.tabulate (emitTripleSelected 2 workspace selection).program
  match TestRun.finishWithin program (cost+1) ⟨0,store⟩ with
  | none => throw (IO.userError "Triple emitter failed to halt at its proved cost")
  | some (steps,finish) =>
      unless steps==cost && (List.finRange 8).all (fun r => finish.store r==expected r) do
        throw (IO.userError "Triple emitter changed a source, scratch, outside register, tail or cost")

def tests : IO Unit := do
  let inputs : List (Fin 3 → Nat×Bool) :=
    [![(0,false),(0,true),(1,false)],![(2,true),(7,false),(31,true)],
      ![(2^128,true),(0,false),(2^128+1,false)]]
  for a in List.finRange 3 do
    for b in List.finRange 3 do
      for c in List.finRange 3 do
        for literals in inputs do
          for tail in [[],[true,false,true]] do checked ![a,b,c] literals tail
  IO.println "Triple emitter passed 162 whole-store executions, including all repeated selections and 129-bit indices."

#eval tests
end Counting.StackMachine.Routine.TripleTests
