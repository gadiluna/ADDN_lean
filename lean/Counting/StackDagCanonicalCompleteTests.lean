import Counting.StackDagCanonicalComplete
import Counting.StackMachineTestLazy

namespace Counting.StackMachine.DagUpdate.Canonical.CompleteTests
open Routine

def cases : List (String×Executable.Vista) :=
  [("initial leader",Executable.initialVista true),
   ("two initial colors",⟨#[⟨0,none,true,0,[]⟩,⟨0,none,false,0,[]⟩],1⟩),
   ("single successor",⟨#[⟨0,none,true,0,[]⟩,⟨1,some 0,true,1,[(0,1)]⟩],1⟩),
   ("duplicate signature",⟨#[⟨0,none,true,0,[]⟩,⟨0,none,true,0,[]⟩,
     ⟨1,some 0,true,1,[(1,1)]⟩],2⟩),
   ("reordered signatures with binary counts",⟨#[⟨0,none,true,0,[]⟩,⟨0,none,false,0,[]⟩,
     ⟨1,some 0,true,2^20,[(1,2^20)]⟩,⟨1,some 1,false,7,[(0,7)]⟩],3⟩)]

def tests : IO Unit := do
  let program := completeCanonical.program
  for (name,source) in cases do
    unless (List.range source.nodes.size).all (Executable.nodeValid source) do
      throw (IO.userError s!"Canonicalization test violates node premises: {name}")
    let initial := inputStore 128 (Encoding.vista.encode source)
    let expected := outputStore 128 (Encoding.vista.encode (Executable.canonicalize source))
    match TestLazy.finishWithin program 10000000 0 (TestLazy.empty program) ⟨0,initial⟩ with
    | none => throw (IO.userError s!"Canonicalizer exceeded fuel: {name}")
    | some (steps,last) =>
      unless (List.finRange 130).all (fun r=>last.store r==expected r) do
        throw (IO.userError s!"Canonicalizer full-store mismatch: {name}")
      IO.println s!"Canonicalization: {name} passed ({steps} instructions)."

#eval tests
end Counting.StackMachine.DagUpdate.Canonical.CompleteTests
