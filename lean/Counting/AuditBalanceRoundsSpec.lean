import Counting.AuditBalanceSpec

namespace Counting.Executable

def auditBalanceRounds (vista : Vista) (weights : Array Nat) (start count : Nat) : Bool :=
  (List.range' start count).all (auditBalanceLevel vista weights)

theorem auditBalanceRounds_zero (vista : Vista) (weights : Array Nat) (start : Nat) :
    auditBalanceRounds vista weights start 0=true := rfl

theorem auditBalanceRounds_succ (vista : Vista) (weights : Array Nat) (start count : Nat) :
    auditBalanceRounds vista weights start (count+1)=
      (auditBalanceLevel vista weights start && auditBalanceRounds vista weights (start+1) count) := by
  simp only [auditBalanceRounds,List.range'_succ,List.all_cons]

/-- The executable audit skips round zero and checks exactly the old
levels zero through `anchor-2`; this includes the empty anchor-zero case. -/
theorem auditBalanceRounds_anchor (vista : Vista) (weights : Array Nat) (anchor : Nat) :
    auditBalanceRounds vista weights 0 (anchor-1)=auditBalance vista weights anchor := by
  apply Bool.eq_iff_iff.mpr
  simp only [auditBalanceRounds,auditBalance,List.all_eq_true,List.mem_range'_1,List.mem_range,
    Nat.zero_le,Nat.zero_add,true_and,Bool.or_eq_true,beq_iff_eq]
  constructor
  · intro checked r inside
    by_cases zero : r=0
    · exact Or.inl zero
    · exact Or.inr (checked (r-1) (by omega))
  · intro checked r inside
    have atNext := checked (r+1) (by omega)
    simpa using atNext

end Counting.Executable
