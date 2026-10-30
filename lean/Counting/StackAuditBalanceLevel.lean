import Counting.AuditBalanceLoopSpec

namespace Counting.StackMachine.AuditBalance
open Routine RealizabilityCheck

/-- A complete level pass is the exact Boolean level check used by the
audit. The node counter comes from the explicit DAG header; obtaining it is
charged separately in the input preparation. -/
theorem levelLoop_all (vista : Executable.Vista) (weights : Array Nat)
    (valid : vista.valid=true) (length : weights.size=vista.nodes.size)
    (round : Nat) (accepted : Bool) (tail : List Bool) (saved : Fin 8 → List Bool)
    (table : saved 0=Encoding.sequence Encoding.node vista.nodes.toList++Encoding.natural.encode vista.bottom)
    (indexEmpty : saved 1=[]) (query : saved 2=round.bits) (flag : saved 3=[])
    (counter : saved 4=List.replicate vista.nodes.size true) :
    ∃ time ≤ levelBudget vista weights round vista.nodes.size,
      Executes levelLoop
        (bankFile (Encoding.vista.encode vista) ((Encoding.array Encoding.natural).encode weights)
          (round+1).bits [] (accepted::tail) saved) time
        (bankFile (Encoding.vista.encode vista) ((Encoding.array Encoding.natural).encode weights)
          (round+1).bits [] ((accepted && Executable.auditBalanceLevel vista weights round)::tail)
          (Function.update (Function.update saved 1 (List.replicate vista.nodes.size true)) 4 [])) := by
  simpa only [rangeCheck_full,loopSaved,Nat.zero_add] using
    levelLoop_executes vista weights valid length round 0 vista.nodes.size (by omega) accepted tail saved
      table indexEmpty query flag counter

end Counting.StackMachine.AuditBalance
