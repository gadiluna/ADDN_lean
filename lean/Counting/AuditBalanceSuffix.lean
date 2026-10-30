import Counting.AuditBalanceSpec

namespace Counting.Executable

/-- Failure of the computed balance test rejects the actual audit suffix
after positive-integral conversion, regardless of the final descendant test. -/
theorem failed_balance_rejects (vista : Vista) (candidate last anchor : Nat)
    (values : Array Rat) (natural : Array Nat)
    (converted : positiveNaturals? values=some natural)
    (failure : auditBalance vista (propagateWeights vista anchor natural) anchor=false) :
    auditSuffix? vista candidate last anchor (some values)=none := by
  simp [auditSuffix?,converted,←auditBalance_eq,failure]

end Counting.Executable
