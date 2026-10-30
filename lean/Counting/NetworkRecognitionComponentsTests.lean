import Counting.NetworkRecognitionLeaderHeader
import Counting.NetworkRecognitionMatrix
import Counting.NetworkRecognitionBFS
import Counting.StackMachineTestLazy

namespace Counting.StackMachine.NetworkRecognition.ComponentsTests
open Routine

private def requireRun {registers:Nat} (name:String) (routine:Routine registers)
    (store expected:Store registers) : IO Nat := do
  let program := routine.program
  match TestLazy.finishWithin program 2000000 0 (TestLazy.empty program) ⟨0,store⟩ with
  | none => throw (IO.userError s!"Network component exhausted fuel: {name}")
  | some (time,result) =>
    unless (List.finRange (registers+2)).all (fun r=>result.store r==expected r) do
      throw (IO.userError s!"Network component violated full-store contract: {name}")
    return time

def tests : IO Unit := do
  let tail := [false,true]
  let suffix := [true,false,true]
  let mut count := 0
  let mut maximum := 0
  for leaders in [[],[false],[true],[false,true,false],[true,true,true],[false,false,false]] do
    let store:Store 19 := fun r=>if r=17 then (Encoding.list Encoding.boolean).encode leaders++suffix
      else if r=1 then true::tail else []
    let time ← requireRun "explicit leader count and suffix" leaderPrefix store (leaderPrefixStore store leaders suffix)
    maximum := max maximum time
    count := count+1
  for value in [0,1,2,3,2^129,2^129+2] do
    let store:Store 2 := fun r=>if r=0 then Encoding.natural.encode value++suffix
      else if r=1 then tail else []
    let time ← requireRun "binary arc positivity" arcBit store (arcBitStore store value suffix)
    maximum := max maximum time
    count := count+1
  for (width,values) in [(0,[]),(1,[0]),(1,[2^129]),(2,[0,2]),(1,[0,2]),(3,[1])] do
    let store:Store 19 := fun r=>if r=17 then (Encoding.list Encoding.natural).encode values++suffix
      else if r=0 then List.replicate width true else if r=1 then true::tail
      else if r=19 then [true,false] else if r=20 then [false,true] else []
    let time ← requireRun "row shape and positivity with preserved outer counter" rowPrefix store
      (rowPrefixStore store true tail values suffix)
    maximum := max maximum time
    count := count+1
  let matrices:List (Nat×List (List Nat)) := [(0,[]),(1,[[0]]),(2,[[0,2],[3,0]]),
    (2,[[0],[1,0]]),(1,[[2^129,0]]),(2,[[0,0],[0,0]])]
  for (width,rows) in matrices do
    let store:Store 19 := fun r=>if r=17 then (Encoding.list (Encoding.list Encoding.natural)).encode rows++suffix
      else if r=0 then List.replicate width true else if r=1 then true::tail else []
    let time ← requireRun "actual matrix dimensions and row-major bits" matrixPrefix store
      (matrixPrefixStore store true tail rows suffix)
    maximum := max maximum time
    count := count+1
  for (width,arcs) in [(0,[]),(1,[false]),(2,[false,true,true,false]),(2,[false,false,false,false])] do
    let store:Store 22 := fun r=>if r=0 then arcs else if r=2 then List.replicate width true
      else if r=19 then true::tail else []
    let expected := Function.update store 19
      (DirectedCounting.strongConnectivityCheck (RealizabilityVerifier.BitGraph.edge width arcs)::tail)
    let time ← requireRun "actual all-active BFS" breadthFirst store expected
    maximum := max maximum time
    count := count+1
  IO.println s!"Network components passed {count} full-store cases; maximum {maximum} instructions."

#eval tests
end Counting.StackMachine.NetworkRecognition.ComponentsTests
