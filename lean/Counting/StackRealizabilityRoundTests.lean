import Counting.StackRealizabilityRoundCorrectness
import Counting.StackMachineTestLazy

namespace Counting.StackMachine.RealizabilityCheck.RoundTests
open Routine

def tests : IO Unit := do
  let initial : Executable.Node := ⟨0,none,true,0,[]⟩
  let child : Executable.Node := ⟨1,some 0,true,1,[(0,1)]⟩
  let inconsistent : Executable.Node := ⟨1,some 0,true,1,[(0,2)]⟩
  let cases : List (List Executable.Node × List Nat × Nat × Nat × Bool) :=
    [([initial,child],[1,1],1,0,true),
     ([initial,inconsistent],[1,1],1,0,true),
     ([initial],[1],2,0,true),
     ([initial,child],[2,1],2,0,false)]
  let mut largest := 0
  for (nodes,values,order,round,accepted) in cases do
    let extra : Fin 3→List Bool := ![[true,false],[false,true,true],[true]]
    let tail := [false,true]
    let store := roundFile (roundInputData nodes values order round (accepted::tail) extra)
    let expected := roundFile (roundInputData nodes values order round
      ((accepted && roundComputedCheck nodes values order round)::tail) extra)
    let program := roundCheck.program
    match TestLazy.finishWithin program 3000000 0 (TestLazy.empty program) ⟨0,store⟩ with
    | none => throw (IO.userError "Complete realizability round exhausted test fuel")
    | some (time,result) =>
      unless (List.finRange 100).all (fun r => result.store r==expected r) do
        throw (IO.userError "Complete realizability round violated full-store result")
      unless time ≤ 1000000000000000000000000*(roundSize nodes values order round)^24 do
        throw (IO.userError "Complete realizability round exceeded proved bound")
      largest := max largest time
  IO.println s!"Complete realizability round passed {cases.length} full-store cases; maximum {largest} instructions."

#eval tests
end Counting.StackMachine.RealizabilityCheck.RoundTests
