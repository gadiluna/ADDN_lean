import Counting.StackAuditPostSolverPolynomial
import Counting.StackMachineTestLazy

namespace Counting.StackMachine.AuditPostSolver.Tests
open Routine

def tests : IO Unit := do
  let p:=complete.program
  let vista : Executable.Vista:=⟨#[⟨0,none,true,0,[]⟩],0⟩
  let cases : List (Nat×Option (Array Rat)):=
    [(1,none),(0,some #[]),(1,some #[1]),(2,some #[1]),(1,some #[(1:Rat)/2])]
  for (candidate,values) in cases do
    let input:=inputWord vista candidate 0 values
    let expected:=outputWord vista candidate 0 values
    let before:=inputStore 54 input
    let after:=outputStore 54 expected
    match TestLazy.finishWithin p 10000000 0 (TestLazy.empty p) ⟨0,before⟩ with
    | none=>throw (IO.userError "Post-solver composition exhausted regression fuel")
    | some (steps,last)=>
      unless (List.finRange (p.extraRegisters+2)).all (fun r=>last.store r==after r) do
        throw (IO.userError "Post-solver result, retained metadata, or workspace cleanup mismatch")
      unless steps≤completeCoefficient*(input.length+1)^51 do
        throw (IO.userError "Post-solver composition exceeded its proved bound")
      IO.println s!"Post-solver candidate {candidate}: {steps} transitions, optional weights {repr (result vista candidate 0 values)}."
  IO.println "Five post-solver regressions passed; all 56 registers checked."

#eval tests
end Counting.StackMachine.AuditPostSolver.Tests
