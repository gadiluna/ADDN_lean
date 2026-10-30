import Counting.StackDagCanonicalCollectEncoding
import Counting.StackMachineTestLazy

namespace Counting.StackMachine.DagUpdate.Canonical.CollectTests
open Routine

def cases : List (String×Array Nat×List Executable.Node×Nat) :=
  [("empty source",#[],[],0),
   ("initial leaders",#[0,1],[⟨0,none,true,0,[]⟩,⟨0,none,false,0,[]⟩],0),
   ("discard other levels",#[1,0],[⟨0,none,true,0,[]⟩,⟨1,some 0,true,3,[(0,3)]⟩],1),
   ("binary counts and missing references",#[2,1],
     [⟨2,some 7,false,2^40,[(9,2^40),(1,3)]⟩,⟨2,some 0,true,7,[(0,4),(1,3)]⟩],2),
   ("unrepresented level",#[0],[⟨0,none,true,0,[]⟩],8)]

def tests : IO Unit := do
  let program := collectRecords.program
  for (name,mapping,nodes,level) in cases do
    let store : Store 94 := fun r=>
      match r.val with
      | 0 => (Encoding.list Encoding.node).encode nodes
      | 1 => (Encoding.array Encoding.natural).encode mapping
      | 64 => [true,false,true]
      | 81 => [true]
      | 82 => level.bits
      | 90 => [false,true]
      | _ => []
    let expected := collectedStore store mapping nodes level
    match TestLazy.finishWithin program 10000000 0 (TestLazy.empty program) ⟨0,store⟩ with
    | none => throw (IO.userError s!"Canonical collector exhausted fuel: {name}")
    | some (steps,last) =>
      unless (List.finRange 96).all (fun r=>last.store r==expected r) do
        throw (IO.userError s!"Canonical collector full-store mismatch: {name}")
      IO.println s!"Canonical collector: {name} passed ({steps} instructions)."

#eval tests
end Counting.StackMachine.DagUpdate.Canonical.CollectTests
