import Counting.StackCompilerComplete

namespace Counting.StackMachine.Compiler.Examples
open Machine

def emptyProgram : StackMachine.Program where
  extraRegisters := 0
  states := 0
  code _ := .halt

def oneProgram : StackMachine.Program where
  extraRegisters := 0
  states := 1
  code control := if control = 0 then .push 1 true 1 else .halt

def finishWithin (program : Machine.Program) : Nat → Machine.Config program → Option (Machine.Config program)
  | 0, _ => none
  | fuel+1, config => match Machine.step program config with
    | none => some config
    | some next => finishWithin program fuel next

def outputIs (program : StackMachine.Program) (input expected : List Bool) : Bool :=
  match finishWithin (compile program) 1000 (Machine.initial (compile program) input) with
  | none => false
  | some result => result.tape.left.all (· == .blank) &&
      (result.tape.head::result.tape.right).takeWhile (· != .blank) == expected.map bitSymbol &&
      ((result.tape.head::result.tape.right).drop expected.length).all (· == .blank)

#guard outputIs emptyProgram [] []
#guard outputIs emptyProgram [true,false,true] []
#guard outputIs oneProgram [] [true]
#guard outputIs oneProgram [false,true,false,true] [true]

end Counting.StackMachine.Compiler.Examples
