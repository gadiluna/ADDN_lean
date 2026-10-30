import Counting.ExternalTransitionLoop

namespace Counting.External.CookLevin.StackGenerator.Tests
open StackMachine StackMachine.Routine

def coordinateTests : IO Unit := do
  let w : CoordinateWorkspace 0 := Function.Embedding.refl _
  let routine := coordinates 0 w
  let mut checked := 0
  for round in List.range 4 do
    for width in List.range 5 do
      for place in List.range (width+1) do
        let store : Fin 12 → List Bool := ![List.replicate round true,List.replicate width true,
          List.replicate place true,[],[],[],[],[false,true],[],[],[true,false,true],[]]
        let expected := coordinateResult w store round width place
        let cost := coordinatesCost round width place
        match Machine.run (step routine.program) cost ⟨0,store⟩ with
        | none => throw (IO.userError "Coordinate routine halted before its exact cost")
        | some result =>
            unless (step routine.program result).isNone do
              throw (IO.userError "Coordinate routine exceeded its exact cost")
            unless (List.finRange 12).all (fun r => result.store r == expected r) do
              throw (IO.userError "Incorrect coordinate or changed unrelated register")
            checked := checked+1
  IO.println s!"Coordinates: {checked} exact-cost stack runs passed, including zero width, singleton rings and boundary positions."

#eval coordinateTests
end Counting.External.CookLevin.StackGenerator.Tests
