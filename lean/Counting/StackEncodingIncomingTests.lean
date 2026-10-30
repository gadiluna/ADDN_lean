import Counting.StackEncodingIncomingCorrectness
import Counting.StackEncodingPairTests

namespace Counting.StackMachine.EncodingPrograms.IncomingTests

def workspace : FullIncomingWorkspace 1 :=
  ⟨fun i=>⟨i.val,by omega⟩,fun a b h=>Fin.ext (congrArg (fun i : Fin 21=>i.val) h)⟩

def prefixStart (input : List Bool) (bound previous : Nat) (first : Bool) : Fin 21 → List Bool :=
  fun r=>if r=0 then input else if r=1 then [true,false]
    else if r=17 then previous.bits else if r=18 then bound.bits
    else if r=19 then [first,true] else if r=20 then [true,false,true] else []

private def requirePrefix (bound previous : Nat) (first : Bool) (input : List Bool) (accepted : Bool) : IO Unit := do
  let base:=prefixStart input bound previous first
  let program:=(incomingPrefix 1 workspace).program
  match PairTests.runUntil program 1000000 ⟨0,base⟩ with
  | none => throw (IO.userError "Incoming prefix exceeded stack test fuel")
  | some (steps,result) =>
    let expected:=incomingScanStore 11 (incomingBodyRoles 1 workspace) base [false] [true]
      (incomingPrefixResult bound.bits input previous.bits first true)
    unless (List.finRange 21).all (fun r=>result.store r==expected r) do
      throw (IO.userError "Incoming prefix full-store mismatch")
    unless result.store 1==[accepted,false] do throw (IO.userError "Incoming prefix graph condition mismatch")
    unless steps≤2500*(input.length+previous.bits.length+bound.bits.length+1)^3 do
      throw (IO.userError "Incoming prefix exceeded verified bound")
    IO.println s!"Incoming full-store: {steps} stack steps, answer {accepted}."

private def requireExact (input : List Bool) (accepted : Bool) : IO Unit := do
  match PairTests.runUntil incomingRecognitionProgram 1000000 (initial incomingRecognitionProgram input) with
  | none => throw (IO.userError "Incoming exact checker exceeded stack test fuel")
  | some (steps,result) =>
    unless result.store 1==[accepted] do throw (IO.userError "Incoming exact checker result mismatch")
    unless steps≤2700*(input.length+1)^3 do throw (IO.userError "Incoming exact checker exceeded verified bound")
    IO.println s!"Incoming exact: {steps} stack steps, answer {accepted}."

private def requirePhysical (input : List Bool) (accepted : Bool) : IO Unit := do
  let machine:=Compiler.compile incomingRecognitionProgram
  match Tests.finishWithin machine 20000000 (Machine.initial machine input) with
  | none => throw (IO.userError "Incoming TM exceeded physical test fuel")
  | some (steps,result) =>
    let right:=result.tape.head::result.tape.right
    unless result.tape.left.all (· == .blank) && right.take 1==[Machine.bitSymbol accepted] &&
        (right.drop 1).all (· == .blank) do
      throw (IO.userError "Incoming TM result or clean tape mismatch")
    unless steps≤(20*(2700+18+5)^2)*(input.length+1)^8 do
      throw (IO.userError "Incoming TM exceeded verified transition bound")
    IO.println s!"Incoming physical TM: {steps} transitions, clean answer {accepted}."

def tests : IO Unit := do
  let encodeEdges:=(Encoding.list (Encoding.product Encoding.natural Encoding.natural)).encode
  for (bound,previous,first,edges,accepted) in
      [(0,0,true,[],true),(4,0,true,[(0,1),(2,2)],true),(4,0,true,[(0,1),(0,3)],false),
       (4,0,true,[(2,1),(1,1)],false),(4,0,true,[(0,0)],false),(4,0,true,[(4,1)],false),
       (4,2,false,[(1,1)],false),(4,2,false,[(3,1)],true),(4,0,true,[(0,2^128)],true)] do
    requirePrefix bound previous first (encodeEdges edges++[true,false,true]) accepted
  requirePrefix 4 0 true [] false
  requirePrefix 4 0 true [true] false
  requirePrefix 4 0 true (Encoding.natural.encode (2^100)) false
  let cases : List (List Bool × Bool) := [
    (incomingInputCodec.encode (0,[]),true),
    (incomingInputCodec.encode (4,[(0,1),(2,2)]),true),
    (incomingInputCodec.encode (4,[(0,1),(0,3)]),false),
    (incomingInputCodec.encode (4,[(2,1),(1,1)]),false),
    (incomingInputCodec.encode (4,[(0,0)]),false),
    (incomingInputCodec.encode (4,[(4,1)]),false),
    (incomingInputCodec.encode (2^129,[(2^128,2^128)]),true),
    ([],false),([true],false),(Encoding.natural.encode 4,false),
    (Encoding.frame [false]++encodeEdges [],false),
    (incomingInputCodec.encode (4,[])++[false],false),
    (Encoding.natural.encode 4++Encoding.natural.encode (2^100),false),
    (Encoding.natural.encode 4++Encoding.natural.encode 1++Encoding.natural.encode 0,false)]
  for (input,accepted) in cases do requireExact input accepted
  for (input,accepted) in [(incomingInputCodec.encode (0,[]),true),
      (incomingInputCodec.encode (2,[(0,1)]),true),(incomingInputCodec.encode (2,[(0,0)]),false),
      (incomingInputCodec.encode (2,[(2,1)]),false),([],false),
      (incomingInputCodec.encode (0,[])++[true],false)] do requirePhysical input accepted
  IO.println "Incoming graph checks passed 12 full-store, 14 exact-stack, 6 physical-TM cases."

#eval tests
end Counting.StackMachine.EncodingPrograms.IncomingTests
