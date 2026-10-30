import Counting.StackEncodingPairMachine
import Counting.StackEncodingTests

namespace Counting.StackMachine.EncodingPrograms.PairTests

def runUntil (program : Program) : Nat → Config program → Option (Nat × Config program)
  | 0,_ => none
  | fuel+1,config => match step program config with
    | none => some (0,config)
    | some next => (runUntil program fuel next).map fun (steps,result) => (steps+1,result)

def registers : Fin 5 → Fin 7 := ![0,1,2,3,4]

def initialStore (input : List Bool) : Fin 7 → List Bool :=
  ![input,[true,false],[false,true],[],[true,true],[false,false],[true,false,true]]

private def requireStore (input first second suffix : List Bool) (accepted : Bool) : IO Unit := do
  let program := (pairRoutine 2 registers).program
  match runUntil program 5000 ⟨0,initialStore input⟩ with
  | none => throw (IO.userError "Pair parser did not halt")
  | some (steps,result) =>
    let expected : Fin 7 → List Bool :=
      ![suffix,first++[true,false],second++[false,true],[],accepted::[true,true],[false,false],[true,false,true]]
    unless (List.finRange 7).all (fun r => result.store r == expected r) do
      throw (IO.userError s!"Pair parser full-store mismatch: {input}")
    unless steps ≤ 6*input.length+13 do throw (IO.userError "Pair parser exceeds stack bound")
    IO.println s!"Pair parser full-store case: {steps} stack steps."

private def requireMachine (input : List Bool) (accepted : Bool) : IO Unit := do
  let program := Compiler.compile pairRecognitionProgram
  match Tests.finishWithin program 300000 (Machine.initial program input) with
  | none => throw (IO.userError "Compiled pair parser did not halt")
  | some (steps,result) =>
    let right := result.tape.head::result.tape.right
    let clean := result.tape.left.all (· == .blank) &&
      right.take 1 == [Machine.bitSymbol accepted] && (right.drop 1).all (· == .blank)
    unless clean do throw (IO.userError "Compiled pair parser wrong or dirty output")
    unless steps ≤ 8820*(input.length+1)^4 do throw (IO.userError "Compiled pair parser exceeds TM bound")
    IO.println s!"Pair parser physical case: {steps} transitions, clean output."

def tests : IO Unit := do
  requireStore [] [] [] [] false
  requireStore [true] [] [] [] false
  requireStore (Encoding.frame [true,false]) [true,false] [] [] false
  requireStore (Encoding.frame [false,true]++[true]) [false,true] [] [] false
  requireStore [false,false] [] [] [] true
  requireStore (Encoding.frame [true,false]++Encoding.frame [false,true]++[true,false])
    [true,false] [false,true] [true,false] true
  requireStore (Encoding.frame [false,false]++Encoding.frame [false]) [false,false] [false] [] true
  for (input,accepted) in [([],false),([true],false),([false],false),([false,true],false),
      ([false,false],true),
      (Encoding.frame [true,false]++Encoding.frame [false,true]++[true],true)] do
    requireMachine input accepted
  IO.println "Pair parser passed 7 arbitrary-store and 6 physical-machine cases."

example : parsePair [false,false] = ⟨[],[],[],true⟩ := rfl
example : parsePair [false,true] = ⟨[],[],[],false⟩ := rfl

#eval tests
end Counting.StackMachine.EncodingPrograms.PairTests
