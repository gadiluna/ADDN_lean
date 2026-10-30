import Counting.StackAuditAscendBinary
import Counting.AuditAscendSpec

namespace Counting.StackMachine.AuditAscend
open Routine

/-- Direct bridge to the executable vista's total node accessor. In
particular an out-of-range lookup returns the parent of the default node. -/
theorem binaryParentAt_vista (store : Store 22) (vista : Executable.Vista) (index : Nat)
    (source : store 17=Encoding.sequence Encoding.node vista.nodes.toList)
    (query : store 21=Encoding.natural.encode index)
    (empty : ∀ r : Fin 24,r≠17 → r≠21 → store r=[]) :
    ∃ time ≤ 200000*((store 17).length+(store 21).length+1)^4,
      Executes binaryParentAt store time
        (Function.update store 2 (indexCode (vista.node index).parent).bits) := by
  simpa only [Array.getElem?_toList,indexCode,DagValidation.parentCode,
    Executable.Vista.node] using binaryParentAt_executes store vista.nodes.toList index source query empty

end Counting.StackMachine.AuditAscend

