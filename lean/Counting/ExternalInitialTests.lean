import Counting.ExternalInitialGenerator

namespace Counting.External.CookLevin.StackGenerator.Tests
open StackMachine StackMachine.Routine InitialRows Tableau

def inertVerifier : Machine.Program where
  states := 0
  code _ _ := none
  accept _ := true

def stackFinishWithin (program : StackMachine.Program) : Nat → Nat → StackMachine.Config program →
    Option (Nat × StackMachine.Config program)
  | 0,_,_ => none
  | fuel+1,elapsed,config => match StackMachine.step program config with
    | none => some (elapsed,config)
    | some next => stackFinishWithin program fuel (elapsed+1) next

def initialTests : IO Unit := do
  let w : InitialWorkspace 0 := Function.Embedding.refl _
  let routine := initialRowRoutine 0 w inertVerifier
  let mut checked := 0
  for header in ([[],[false],[true,false]] : List (List Bool)) do
    for capacity in List.range 3 do
      let width := 2+header.length+capacity
      let setup : Setup width := ⟨⟨1,by omega⟩,header,capacity,by dsimp; omega⟩
      let store : Fin 24 → List Bool := fun r =>
        if r=1 then [true] else if r=2 then header else if r=3 then List.replicate capacity true
        else if r=4 then List.replicate width true else if r=5 then [false,true]
        else if r=16 then [true,false,true] else []
      let expected := Encoding.sequence clauseCodec
        (((setup.constraints inertVerifier).map (initialConstraint (T:=0))).flatMap
          (fun c => c.toCNF.map (List.map CNFEncoding.literalRaw)))++[false,true]
      match stackFinishWithin routine.program 1000000 0 ⟨0,store⟩ with
      | none => throw (IO.userError "Initial-row generator exhausted stack transition fuel")
      | some (elapsed,finish) =>
          unless finish.store (w 5)==expected do
            throw (IO.userError "Initial-row generator changed clause order or content")
          unless (List.finRange 24).all (fun r => r=5 || finish.store r==store r) do
            throw (IO.userError "Initial-row generator did not restore scratch or preserve input")
          unless elapsed ≤ initialRowBound inertVerifier width capacity do
            throw (IO.userError "Initial-row generator exceeded its proved stack-time bound")
          checked := checked+1
  IO.println s!"Initial row: {checked} actual stack runs passed, including empty headers, zero/one capacity, witness adjacency, preserved input and scratch cleanup."

#eval initialTests
end Counting.External.CookLevin.StackGenerator.Tests
