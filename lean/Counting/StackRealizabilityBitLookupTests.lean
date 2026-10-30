import Counting.StackRealizabilityBitLookup
import Counting.StackDagTestRun

namespace Counting.StackMachine.RealizabilityCheck.BitLookupTests
open Routine

def roles : Fin 7 ↪ Fin 7:=Function.Embedding.refl _

private def test (input : List Bool) (index : Nat) : IO Unit:=do
  let store : Store 5:=fun r=>if r=0 then input else if r=1 then List.replicate index true
    else if r=2 then [true,false] else if r=3 then [false,true] else []
  let expected:=Function.update store 2
    (RealizabilityVerifier.BitGraph.bitAt input index::store 2)
  match DagValidation.TestRun.run (bitLookup 0 roles).program 100000 0 ⟨0,store⟩ with
  | none=>throw (IO.userError "Graph bit lookup exceeded test fuel")
  | some (time,result)=>
    unless (List.finRange 7).all (fun r=>result.store r==expected r) do
      throw (IO.userError "Graph bit lookup violated its full-store/default-false contract")
    unless time≤6*input.length+7*index+16 do
      throw (IO.userError "Graph bit lookup exceeded its linear instruction bound")

def tests : IO Unit:=do
  for input in [[],[false],[true],[true,false,true,false]] do
    for index in [0,1,input.length,input.length+2] do test input index
  test [true,false] 129
  test [false,true] 0
  IO.println "Graph bit lookup passed 18 full-store/default-false cases with preserved source, index, and flag tail."

#eval tests
end Counting.StackMachine.RealizabilityCheck.BitLookupTests
