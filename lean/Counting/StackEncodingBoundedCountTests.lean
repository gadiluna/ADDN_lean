import Counting.StackEncodingBoundedCount
import Counting.StackEncodingPairTests

namespace Counting.StackMachine.EncodingPrograms.CountTests

def workspace : CountWorkspace 1 :=
  ⟨fun i => ⟨i.val,Nat.lt_trans i.isLt (by decide)⟩,by intro a b same; exact Fin.ext (congrArg (fun x : Fin 12 => x.val) same)⟩

def base : Fin 12 → List Bool := fun r => if r=6 then [false,true] else if r=11 then [true,false,false] else []

private def require (header : List Bool) (budget result : Nat) (accepted : Bool) : IO Unit := do
  let program := (boundedCount 1 workspace).program
  let input := countState 1 workspace base header 0 (List.replicate budget true)
  match PairTests.runUntil program 200000 ⟨0,input⟩ with
  | none => throw (IO.userError "Bounded count exhausted transitions")
  | some (steps,finish) =>
    let expected := Function.update (countState 1 workspace base header result []) (workspace 6) (accepted::base (workspace 6))
    unless (List.finRange 12).all (fun r => finish.store r==expected r) do
      throw (IO.userError s!"Bounded count wrong store: header={header}, budget={budget}")
    unless steps ≤ 64*(budget+(Encoding.frame header).length+1)^3 do
      throw (IO.userError "Bounded count exceeded proved cost")
    IO.println s!"Bounded count: budget {budget}, result {result}, accepted {accepted}, {steps} stack steps."

def tests : IO Unit := do
  require [] 0 0 true
  require [] 3 0 true
  require (1:Nat).bits 0 0 false
  require (3:Nat).bits 2 2 false
  require (3:Nat).bits 3 3 true
  require (3:Nat).bits 5 3 true
  require [false] 3 3 false
  require [true,false] 3 3 false
  require (2^100:Nat).bits 2 2 false
  IO.println "Bounded count passed 9 cap, canonicality, empty-budget, preservation, and huge-header cases."

example : countRun (3:Nat).bits 0 2 = 2 := by decide
example : countRun (3:Nat).bits 0 5 = 3 := by decide
example : countRun [false] 0 3 = 3 := by decide

#eval tests
end Counting.StackMachine.EncodingPrograms.CountTests
