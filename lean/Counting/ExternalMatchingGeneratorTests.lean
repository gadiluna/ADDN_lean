import Counting.ExternalMatchingVariableOuter
import Counting.ExternalMatchingCompletionLoop
import Counting.StackMachineTestMemo

namespace Counting.External.MatchingMachine.Tests
open StackMachine

private def variableWorkspace : VariableOuterWorkspace 2 :=
  ⟨fun i=>⟨i.val,by omega⟩,by intro a b h;exact Fin.ext (congrArg (fun i : Fin 18=>i.val) h)⟩
private def completionWorkspace : RowWorkspace 2 :=
  ⟨fun i=>⟨i.val,by omega⟩,by intro a b h;exact Fin.ext (congrArg (fun i : Fin 17=>i.val) h)⟩

private def checked {width : Nat} (program : Program) (registers : program.extraRegisters+2=width)
    (initial expected : Fin width → List Bool) (fuel : Nat) : IO Nat := do
  let store : Fin (program.extraRegisters+2) → List Bool := fun r=>initial (r.cast registers)
  match TestRun.finishWithin program fuel ⟨0,store⟩ with
  | none => throw (IO.userError "matching generator loop exceeded its proved bound")
  | some (steps,finish) =>
    unless (List.finRange (program.extraRegisters+2)).all (fun r=>finish.store r==expected (r.cast registers)) do
      throw (IO.userError "matching generator changed a coordinate, stream, scratch or external register")
    pure steps

def tests : IO Unit := do
  let variableProgram := TestRun.tabulate (emitVariables 2 variableWorkspace).program
  let completionProgram := TestRun.tabulate (emitCompletion 2 completionWorkspace).program
  let mut maximum := 0
  for base in [0,2] do
    for normal in [0,1,3,6] do
      for count in [0,1,2] do
        let store : Fin 18 → List Bool := fun r=>
          if r=0 then List.replicate base true else if r=2 then List.replicate (base+7) true
          else if r=13 then List.replicate normal true else if r=15 then List.replicate count true
          else if r=6 then [false,true] else if r=16 then [true,false,true] else if r=17 then [false,false] else []
        let limit := base+(base+7)+normal+2*count*(normal+1)
        let steps ← checked variableProgram rfl store (variablesResult 2 variableWorkspace store count)
          (count*(8000*(limit+1)^3+2)+2)
        maximum := max maximum steps
  for base in [0,3] do
    for ports in [0,1,3] do
      for count in [0,1,2] do
        let store : Fin 17 → List Bool := fun r=>
          if r=0 ∨ r=1 then List.replicate base true else if r=13 then List.replicate ports true
          else if r=14 then List.replicate count true else if r=6 then [false,true]
          else if r=15 then [true,false,true] else if r=16 then [false,false] else []
        let limit := 2*base+ports+2*count
        let steps ← checked completionProgram rfl store (completionResult 2 completionWorkspace store count)
          (count*(320*(limit+1)^3+2)+2)
        maximum := max maximum steps
  IO.println s!"Matching generator: 24 variable-cycle and 18 completion-loop full-store runs passed; singleton cycles, empty ranges, suffix streams and external sentinels checked; maximum {maximum} stack transitions."

#eval tests
end Counting.External.MatchingMachine.Tests
