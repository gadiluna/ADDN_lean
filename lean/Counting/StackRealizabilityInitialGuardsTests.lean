import Counting.StackRealizabilityInitialGuards
import Counting.StackDagTestRun

namespace Counting.StackMachine.RealizabilityCheck.InitialGuardsTests
open Routine

private def requireBounds (leaders nonleaders ell order : Nat) (accepted expected : Bool) : IO Unit:=do
  let store : Store 8:=![leaders.bits,nonleaders.bits,ell.bits,order.bits,accepted::[false,true],[],[],[],[],[]]
  unless initialBoundsCheck leaders nonleaders ell order==expected do
    throw (IO.userError "Incorrect expected initial-bound specification")
  match DagValidation.TestRun.run initialBoundsGuard.program 1000000 0 ⟨0,store⟩ with
  | none=>throw (IO.userError "Initial-bound guard exceeded test fuel")
  | some (steps,result)=>
    let final:=Function.update store 4 ((accepted&&expected)::[false,true])
    unless (List.finRange 10).all (fun r=>result.store r==final r) do
      throw (IO.userError "Initial-bound guard changed preserved operands/scratch or returned an incorrect flag")
    unless steps≤100*(leaders.size+nonleaders.size+ell.size+order.size+1) do
      throw (IO.userError "Initial-bound guard exceeded its bit-linear bound")
    IO.println s!"Initial bounds: {steps} stack instructions; full store preserved except status."

def tests : IO Unit:=do
  requireBounds 0 0 0 0 true false
  requireBounds 0 0 0 9 true false
  requireBounds 0 0 2 1 true false
  requireBounds 1 0 1 1 true true
  requireBounds 2 0 1 3 true false
  requireBounds 1 3 1 3 true false
  requireBounds 1 2 1 3 true true
  requireBounds 0 0 2 2 true true
  requireBounds 0 1 2 2 true false
  requireBounds 2 5 3 8 false true
  requireBounds (2^128) (2^128-1) (2^128) (2^129-1) true true
  requireBounds (2^128) (2^128) (2^128) (2^129-1) true false
  IO.println "Initial-bound guard passed 12 exact full-store tests, including 129-bit counts and saturated-subtraction boundaries."

#eval tests
end Counting.StackMachine.RealizabilityCheck.InitialGuardsTests
