import Counting.StackRealizabilityRoundGuards
import Counting.StackDagTestRun

namespace Counting.StackMachine.RealizabilityCheck.RoundGuardsTests
open Routine

private def requireBounds (child weight supply demand visible order : Nat)
    (accepted expected : Bool) : IO Unit := do
  let store : Store 8 := ![child.bits,weight.bits,supply.bits,demand.bits,visible.bits,order.bits,
    accepted::[false,true],[],[],[]]
  unless roundBoundsCheck child weight supply demand visible order==expected do
    throw (IO.userError "Round guard reference expectation mismatch")
  match DagValidation.TestRun.run roundBoundsGuard.program 1000000 0 ⟨0,store⟩ with
  | none=>throw (IO.userError "Round guard exhausted test fuel")
  | some (steps,result)=>
    let final:=Function.update store 6 ((accepted&&expected)::[false,true])
    unless (List.finRange 10).all (fun r=>result.store r==final r) do
      throw (IO.userError "Round guard returned an incorrect status or changed operands/scratch")
    unless steps ≤ 100*(child.size+weight.size+supply.size+demand.size+visible.size+order.size+1) do
      throw (IO.userError "Round guard exceeded its bit-linear bound")
    IO.println s!"Round guard: {steps} stack instructions; exact whole-store result."

def tests : IO Unit := do
  requireBounds 0 0 0 0 0 0 true true
  requireBounds 2 1 3 3 3 3 true false
  requireBounds 1 1 3 3 3 3 true true
  requireBounds 1 2 3 4 3 3 true false
  requireBounds 1 2 4 3 3 3 true false
  requireBounds 1 2 4 4 5 3 true true
  requireBounds 1 2 3 4 5 3 true false
  requireBounds 1 2 0 999 2 3 true true
  requireBounds 2 2 3 3 2 3 true true
  requireBounds 2 2 4 3 2 3 true true
  requireBounds 2 2 3 4 2 3 true false
  requireBounds 3 2 0 0 2 3 true false
  requireBounds 1 2 3 3 3 3 false true
  requireBounds 1 1 0 1 0 1 false false
  requireBounds (2^128) (2^128) (2^129) (2^129-1) (2^128) (2^128+1) true true
  requireBounds (2^128) (2^128) (2^129-1) (2^129) (2^128) (2^128+1) true false
  requireBounds (2^128-1) (2^128) 0 (2^129) (2^128) (2^128+1) true true
  IO.println "Round guards passed 17 full-store cases, including empty hidden classes, positive leaving counts, saturated subtraction and 130-bit values."

#eval tests
end Counting.StackMachine.RealizabilityCheck.RoundGuardsTests
