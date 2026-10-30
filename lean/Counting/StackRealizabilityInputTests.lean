import Counting.StackRealizabilityInputSyntax
import Counting.StackRealizabilityInputShape
import Counting.StackRealizabilityInputBottom
import Counting.StackRealizabilityInputInitial
import Counting.StackMachineTestLazy

namespace Counting.StackMachine.RealizabilityCheck.InputTests
open Routine

private def requireRun (name : String) (routine : Routine 98) (start finish : Store 98) : IO Nat := do
  let program := routine.program
  match TestLazy.finishWithin program 3000000 0 (TestLazy.empty program) ⟨0,start⟩ with
  | none => throw (IO.userError s!"Realizability input stage exhausted fuel: {name}")
  | some (time,result) =>
    unless (List.finRange 100).all (fun r=>result.store r==finish r) do
      throw (IO.userError s!"Realizability input stage violated full-store result: {name}")
    return time

def tests : IO Unit := do
  let a : Executable.Node := ⟨0,none,true,0,[]⟩
  let b : Executable.Node := ⟨1,some 0,true,0,[]⟩
  let vista : Executable.Vista := ⟨#[a,b],1⟩
  let tail := [false,true]
  let mut count := 0
  let mut largest := 0
  for (values,ell,order) in [([1,1],1,1),([2^100,1],2^90,2^110)] do
    let input := Encoding.verifierInput.encode (vista,values,ell,order)
    let time ← requireRun "canonical component split" inputSplit (inputSplitStore input (true::tail))
      (inputFieldsStore vista values ell order (true::tail))
    largest := max largest time
    count := count+1
  for values in [[1,1],[0,1],[1]] do
    let status := countsShapeCheck values.toArray vista.nodes.size
    let time ← requireRun "count positivity and dimension" inputShape
      (inputCountStore vista values 1 1 (true::tail)) (inputCountStore vista values 1 1 (status::tail))
    largest := max largest time
    count := count+1
  for values in [[1,1],[1,2]] do
    let status := decide (RealizabilityVerifier.weight values.toArray vista.bottom=1)
    let time ← requireRun "bottom count" inputBottom
      (inputCountStore vista values 1 2 (true::tail)) (inputCountStore vista values 1 2 (status::tail))
    largest := max largest time
    count := count+1
  for (values,ell,order) in [([1,1],1,1),([2,1],1,1)] do
    let status := initialScanCheck vista.nodes.toList values ell order
    let time ← requireRun "initial capacities" inputInitial
      (inputCountStore vista values ell order (true::tail)) (inputCountStore vista values ell order (status::tail))
    largest := max largest time
    count := count+1
  let encoded := Encoding.verifierInput.encode (vista,[1,1],1,1)
  for input in [[],encoded,encoded++[true]] do
    let time ← requireRun "total syntax" inputSyntax (inputSyntaxStart input)
      (inputSyntaxStore input [(Encoding.verifierInput.decodeExact input).isSome])
    largest := max largest time
    count := count+1
  IO.println s!"Realizability input stages passed {count} full-store cases; maximum {largest} instructions."

#eval tests
end Counting.StackMachine.RealizabilityCheck.InputTests
