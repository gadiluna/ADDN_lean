import Counting.StackEncodingDagReadPreserving
import Counting.StackEncodingDagReadTests

namespace Counting.StackMachine.EncodingPrograms.DagParser.PreservingReadTests

def reverseRoles : Fin 20 ↪ Fin 23 where
  toFun r:=⟨19-r.val,by omega⟩
  inj':=by
    intro a b equal
    have h:=congrArg (fun r:Fin 23=>r.val) equal
    apply Fin.ext
    have aBound:=a.isLt
    have bBound:=b.isLt
    change 19-a.val=19-b.val at h
    omega

def extend (store : Fin 20→List Bool) : Fin 23→List Bool := fun r=>
  if h:r.val<20 then store ⟨19-r.val,by omega⟩ else [true,false,true]

private def requireRead (input index : List Bool) (accepted : Bool) : IO Unit := do
  let store : Fin 20→List Bool := fun r=>
    if r=1 then [accepted,false,true] else if r=17 then input else if r=18 then index else []
  let effect:=nodeReadEffect index.length input
  let expected:=preservingNodeStore store accepted [false,true] effect
  match PairTests.runUntil preservingNodeRead.program 2000000 ⟨0,store⟩ with
  | none=>throw (IO.userError "Preserving node reader exceeded stack test budget")
  | some (steps,result)=>
    unless (List.finRange 20).all (fun r=>result.store r==expected r) do
      throw (IO.userError "Preserving node reader changed its source, index, status tail or workspace")
    unless steps≤(2*index.length+3)*2029*(input.length+1)^3+6*input.length+7*index.length+14 do
      throw (IO.userError "Preserving node reader exceeded proved step bound")
    let relocated:=Routine.relocate preservingNodeRead reverseRoles
    match PairTests.runUntil relocated.program 2000000 ⟨0,extend store⟩ with
    | none=>throw (IO.userError "Relocated preserving reader exceeded stack test budget")
    | some (relocatedSteps,relocatedResult)=>
      unless relocatedSteps==steps do
        throw (IO.userError "Register relocation changed the exact number of steps")
      unless (List.finRange 23).all (fun r=>relocatedResult.store r==extend expected r) do
        throw (IO.userError "Relocated reader changed an external sentinel or produced a wrong result")
      IO.println s!"Preserving node access: {steps} stack steps; reversed relocation has the same cost."

def tests : IO Unit := do
  let code:=Encoding.sequence Encoding.node ReadTests.values
  requireRead code [] true
  requireRead code [false,true] true
  requireRead code [true,false,true] true
  requireRead [] [] true
  requireRead [true] [] false
  requireRead (Encoding.node.encode Tests.initialNode++[true,false]) [] false
  IO.println "Preserving node access passed 6 complete stores and 6 reversed-register relocations."

#eval tests
end Counting.StackMachine.EncodingPrograms.DagParser.PreservingReadTests
