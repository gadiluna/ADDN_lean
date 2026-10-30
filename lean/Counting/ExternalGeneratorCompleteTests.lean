import Counting.ExternalGeneratorProgram
import Counting.ExternalInitialTests

namespace Counting.External.CookLevin.StackGenerator.Tests
open StackMachine

/-- Optional interpreter regression. The fixed finite control for transition
clauses is large, so this is kept out of ordinary module compilation. -/
def completeGeneratorTests : IO Unit := do
  let generated := stackGenerator inertVerifier 0 0 0 0
  for input in ([[],[true]] : List (List Bool)) do
    match stackFinishWithin generated 2000000 0 (StackMachine.initial generated input) with
    | none => throw (IO.userError "Complete generator exhausted stack fuel")
    | some (elapsed,finish) =>
        unless finish.store 1==reduce inertVerifier 0 0 0 0 input do
          throw (IO.userError "Complete generator differed from the exact CNF codec")
        unless finish.store 0==input do
          throw (IO.userError "Complete generator changed the preserved input")
        unless elapsed≤generatorCost inertVerifier input 0 0 0 0 do
          throw (IO.userError "Complete generator exceeded the proved instruction bound")
  IO.println "Complete Cook-Levin generator: 2 actual stack runs passed, including empty input and exact whole CNF encoding."

end Counting.External.CookLevin.StackGenerator.Tests
