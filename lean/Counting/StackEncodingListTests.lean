import Counting.StackEncodingArrayMachine
import Counting.StackEncodingPairTests

namespace Counting.StackMachine.EncodingPrograms.ListTests

def workspace : FullListWorkspace 1 where
  toFun i := ⟨i.val,by omega⟩
  inj' := by intro a b same; apply Fin.ext; exact congrArg (fun r : Fin 18 => r.val) same

def base (input : List Bool) : Fin 18 → List Bool :=
  fun r => if r=0 then input else if r=1 then [true,false]
    else if r=17 then [false,true,true] else []

private def requirePrefix (input body suffix : List Bool) (accepted : Bool) : IO Unit := do
  let program := (listPrefixRoutine 1 workspace).program
  match PairTests.runUntil program 300000 ⟨0,base input⟩ with
  | none => throw (IO.userError "List prefix parser did not halt")
  | some (steps,result) =>
    let expected : Fin 18 → List Bool := fun r =>
      if r=0 then suffix else if r=1 then accepted::[true,false]
      else if r=2 then body else if r=17 then [false,true,true] else []
    unless (List.finRange 18).all (fun r => result.store r == expected r) do
      throw (IO.userError s!"List prefix parser full-store mismatch for {input}")
    unless steps ≤ 1900*(input.length+1)^3 do throw (IO.userError "List parser exceeds stack bound")
    IO.println s!"List prefix parser: {steps} stack steps, status {accepted}."

private def requireMachine (input : List Bool) (accepted : Bool) : IO Unit := do
  let program := Compiler.compile listRecognitionProgram
  match Tests.finishWithin program 3000000 (Machine.initial program input) with
  | none => throw (IO.userError "Compiled list validator did not halt within test budget")
  | some (steps,result) =>
    let right := result.tape.head::result.tape.right
    let clean := result.tape.left.all (· == .blank) &&
      right.take 1 == [Machine.bitSymbol accepted] && (right.drop 1).all (· == .blank)
    unless clean do throw (IO.userError "Compiled list validator wrong or dirty output")
    unless steps ≤ 75272000*(input.length+1)^8 do throw (IO.userError "List validator exceeds TM bound")
    IO.println s!"List validator: {steps} physical transitions, clean result {accepted}."

def tests : IO Unit := do
  requirePrefix [] [] [] false
  requirePrefix [true] [] [] false
  requirePrefix ((Encoding.list Encoding.natural).encode []) [] [] true
  requirePrefix ((Encoding.list Encoding.natural).encode [0]) [false] [] true
  requirePrefix ((Encoding.list Encoding.natural).encode [1,2]) (Encoding.sequence Encoding.natural [1,2]) [] true
  requirePrefix ((Encoding.list Encoding.natural).encode [1,2]++[true,false])
    (Encoding.sequence Encoding.natural [1,2]) [true,false] true
  requirePrefix (Encoding.natural.encode 1) [] [] false
  requirePrefix (Encoding.natural.encode 1++[true]) [false] [] false
  requirePrefix (Encoding.natural.encode 1++Encoding.frame [false]) (Encoding.frame [false]) [] false
  requirePrefix (Encoding.frame [false]++[false]) [false] [] false
  requirePrefix [false,true] [] [true] true
  requirePrefix (Encoding.natural.encode (2^100)++[false]) [false] [] false
  requirePrefix (Encoding.natural.encode 2++[false]) [false] [] false
  for (input,accepted) in [([],false),([true],false),([false],true),([false,true],false),
      ((Encoding.list Encoding.natural).encode [0],true),
      ((Encoding.list Encoding.natural).encode [1],true),
      (Encoding.natural.encode 1++Encoding.frame [false],false)] do
    requireMachine input accepted
  IO.println "List codec passed 13 full-store and 7 compiled Turing-machine cases."

example : listCheck [false]=true := rfl
example : listCheck [false,true]=false := rfl
example : listCheck ((Encoding.list Encoding.natural).encode [0,1,2])=true := listCheck_encode _

#eval tests
end Counting.StackMachine.EncodingPrograms.ListTests
