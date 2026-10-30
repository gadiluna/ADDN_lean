import Counting.StackAuditBalanceLoop

namespace Counting.StackMachine.AuditBalance

theorem rangeCheck_eq_all (vista : Executable.Vista) (weights : Array Nat) (round start count : Nat) :
    rangeCheck vista weights round start count=
      (List.range' start count).all (selectedCheck vista weights round) := by
  induction count generalizing start with
  | zero=>simp [rangeCheck]
  | succ count ih=>simp only [rangeCheck,List.range'_succ,List.all_cons,ih]

theorem rangeCheck_full (vista : Executable.Vista) (weights : Array Nat) (round : Nat) :
    rangeCheck vista weights round 0 vista.nodes.size=Executable.auditBalanceLevel vista weights round := by
  rw [rangeCheck_eq_all,←List.range_eq_range']
  rfl

end Counting.StackMachine.AuditBalance
