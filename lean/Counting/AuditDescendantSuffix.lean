import Counting.AuditDescendantSpec
import Counting.AuditPostSolverSpec

namespace Counting.Executable

/-- Exact interface between the completed post-solver computation and
the last two finite descendant scans. -/
theorem auditSuffix_after_descendant_check (vista : Vista) (candidate last anchor : Nat)
    (values : Option (Array Rat)) :
    auditSuffix? vista candidate last anchor values = do
      let weights←StackMachine.AuditPostSolver.result vista candidate anchor values
      if !auditDescendants vista weights anchor last then none else return ⟨anchor,weights⟩ := by
  rw [StackMachine.AuditPostSolver.auditSuffix_after_result]
  simp only [auditDescendants_eq]

end Counting.Executable
