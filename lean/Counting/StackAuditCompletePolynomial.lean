import Counting.StackAuditCompleteBudgetBounds

namespace Counting.StackMachine.AuditComplete
open Routine

/-- A uniform polynomial bound on actual stack instructions for the entire
audit, including all input/output work, guards, solver, scans, and erasure. -/
theorem complete_polynomial : ∃ coefficient degree,
    ∀ (vista : Executable.Vista) (leaders candidate last : Nat),
      ∃ time≤ coefficient*((AuditPrefix.inputWord vista leaders candidate last).length+1)^degree,
        Executes complete (inputStore 62 (AuditPrefix.inputWord vista leaders candidate last)) time
          (outputStore 62 (witnessWord (Executable.audit? vista leaders candidate last))) := by
  obtain ⟨coefficient,degree,polynomial⟩:=completeCostBound_poly
  refine ⟨coefficient,degree,?_⟩
  intro vista leaders candidate last
  obtain ⟨time,bound,run⟩:=complete_executes vista leaders candidate last
  exact ⟨time,bound.trans ((completeBudget_bounded vista leaders candidate last).trans
    (polynomial _ (by omega))),run⟩

end Counting.StackMachine.AuditComplete
