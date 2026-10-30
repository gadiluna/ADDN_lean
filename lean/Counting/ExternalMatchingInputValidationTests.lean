import Counting.ExternalMatchingInputValidation
import Counting.StackMachineTestLazy

namespace Counting.External.MatchingInputValidation.Tests
open StackMachine StackMachine.Routine

private def roles : SATVerification.SATWorkspace 2:=
  ⟨fun i=>⟨i.val,by omega⟩,by intro i j same;exact Fin.ext (congrArg (fun v : Fin 34=>v.val) same)⟩

private def require (input : List Bool) (expected : Bool) : IO Unit := do
  unless validInput input==expected do
    throw (IO.userError "Matching input validity expectation mismatch")
  let store : Store 32:=fun r=>
    if r=0 then input else if r=1 then [true]
    else if r=32 then [false,true,true] else if r=33 then [true,false] else []
  let program:=(routine 2 roles).program
  let wanted:=result 2 roles store
  match TestLazy.finishWithin program 3000000 0 (TestLazy.empty program) ⟨0,store⟩ with
  | none=>throw (IO.userError "Matching input validator exhausted test fuel")
  | some (steps,finished)=>
    unless (List.finRange 34).all (fun r=>finished.store r==wanted r) do
      throw (IO.userError "Matching validator full-store contract failed")
    unless finished.store 1==[expected] do
      throw (IO.userError "Matching validator accepted/rejected incorrectly")
    unless steps ≤ coefficient*(input.length+1)^5 do
      throw (IO.userError "Matching validator exceeded proved polynomial bound")
    IO.println s!"Matching input validation: {steps} stack steps; exact status, counters, cleanup and external sentinels."

def tests : IO Unit := do
  for (raw,expected) in ([
      (([],[]),true),(([true],[]),true),(([true],[[0,0,0]]),true),
      (([true,true],[[0,1,0],[1,0,1]]),true),
      (([],[[0,0,0]]),false),(([false],[]),false),(([true,false],[[0,0,0]]),false),
      (([true],[[1,0,0]]),false),(([true],[[0,1,0]]),false),(([true],[[0,0,1]]),false),
      (([true],[[0,0]]),false),(([true],[[0,0,0,0]]),false),
      (([true],[[2^128,0,0]]),false),(([true,true],[[0,0,0],[0,0,2^128]]),false)] :
      List (ThreeDMEncoding.Raw×Bool)) do
    require (ThreeDMEncoding.rawCodec.encode raw) expected
  require [] false
  require [true] false
  require ((ThreeDMEncoding.rawCodec.encode ([],[]))++[false]) false
  require (Encoding.natural.encode (2^128)) false
  IO.println "Matching input validator passed 18 full-store cases, including malformed syntax, exact triple width, all coordinate positions, false markers and 129-bit out-of-range indices."

#eval tests
end Counting.External.MatchingInputValidation.Tests
