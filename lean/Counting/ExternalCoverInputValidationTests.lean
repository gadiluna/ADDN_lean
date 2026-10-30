import Counting.ExternalCoverInputValidation
import Counting.StackMachineTestLazy

namespace Counting.External.CoverInputValidation.Tests
open StackMachine StackMachine.Routine

private def roles : SATVerification.SATWorkspace 2:=
  ⟨fun i=>⟨i.val,by omega⟩,by intro i j same;exact Fin.ext (congrArg (fun v : Fin 34=>v.val) same)⟩

private def require (input : List Bool) (expected : Bool) : IO Unit := do
  unless validInput input==expected do
    throw (IO.userError "X3C input validity expectation mismatch")
  let store : Store 32:=fun r=>
    if r=0 then input else if r=1 then [true]
    else if r=32 then [false,true,true] else if r=33 then [true,false] else []
  let program:=(routine 2 roles).program
  let wanted:=result 2 roles store
  match TestLazy.finishWithin program 3000000 0 (TestLazy.empty program) ⟨0,store⟩ with
  | none=>throw (IO.userError "X3C input validator exhausted test fuel")
  | some (steps,finished)=>
    unless (List.finRange 34).all (fun r=>finished.store r==wanted r) do
      throw (IO.userError "X3C validator full-store contract failed")
    unless finished.store 1==[expected] do
      throw (IO.userError "X3C validator accepted/rejected incorrectly")
    unless steps ≤ coefficient*(input.length+1)^5 do
      throw (IO.userError "X3C validator exceeded proved polynomial bound")
    IO.println s!"X3C input validation: {steps} stack steps; exact status, counters, cleanup and external sentinels."

def tests : IO Unit := do
  let cases : List (X3CEncoding.Raw×Bool):=[
    (([],[]),true),(([true],[]),false),(([true,true],[]),false),
    ((List.replicate 3 true,[]),true),((List.replicate 3 true,[[0,1,2]]),true),
    ((List.replicate 6 true,[[0,1,2],[3,4,5]]),true),
    ((List.replicate 3 true,[[0,1,2],[0,1,2]]),true),
    ((List.replicate 4 true,[[0,1,2]]),false),
    (([],[[0,1,2]]),false),(([true,false,true],[]),false),
    ((List.replicate 3 true,[[0,0,2]]),false),
    ((List.replicate 3 true,[[0,1,1]]),false),
    ((List.replicate 3 true,[[0,2,1]]),false),
    ((List.replicate 3 true,[[1,0,2]]),false),
    ((List.replicate 3 true,[[1,2,0]]),false),
    ((List.replicate 3 true,[[2,0,1]]),false),
    ((List.replicate 3 true,[[2,1,0]]),false),
    ((List.replicate 3 true,[[0,1]]),false),
    ((List.replicate 3 true,[[0,1,2,2]]),false),
    ((List.replicate 3 true,[[0,1,3]]),false),
    ((List.replicate 3 true,[[2^128,1,2]]),false),
    ((List.replicate 3 true,[[0,1,2^128]]),false)]
  for (raw,expected) in cases do require (X3CEncoding.rawCodec.encode raw) expected
  require [] false
  require [true] false
  require ((X3CEncoding.rawCodec.encode ([],[]))++[false]) false
  require (Encoding.natural.encode (2^128)) false
  IO.println "X3C input validator passed 26 full-store cases: exact syntax, divisibility, ordering, duplicate elements/rows, ranges, huge indices and preserved external registers."

#eval tests
end Counting.External.CoverInputValidation.Tests
