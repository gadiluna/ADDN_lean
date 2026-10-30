import Counting.StackCoreAuditComplete
import Counting.ExecutableRefinementCore

namespace Counting.StackMachine.CoreAudit

theorem answer_eq_coreScheduledPlan (vista : Executable.Vista) (leaders : Nat) (positive : 0<leaders) :
    answer vista leaders (vista.node vista.bottom).level=(Executable.coreScheduledPlan leaders vista).eval := by
  change answer vista leaders (vista.node vista.bottom).level=Executable.coreScheduledOutput leaders vista
  rw [Executable.coreScheduledOutput_unfold]
  let round:=(vista.node vista.bottom).level
  change answer vista leaders round=
    if leaders≤ (round+1)/2 ∧ round=2*((round+1)/2)-1 then
      if (Executable.audit? vista leaders ((round+1)/2) ((round+1)/2)).isSome then some ((round+1)/2) else none
    else none
  unfold answer CoreSchedule.candidate
  by_cases odd:round%2=1
  · have half:(round+1)/2=round/2+1 := by omega
    have depth:round=2*(round/2+1)-1 := by omega
    simp only [odd,if_true,half]
    by_cases eligible:leaders≤ round/2+1
    · rw [if_pos eligible,if_pos ⟨eligible,depth⟩]
      rfl
    · rw [if_neg eligible,if_neg (by intro h;exact eligible h.1)]
      rfl
  · have absent:¬(leaders≤ (round+1)/2 ∧ round=2*((round+1)/2)-1) := by omega
    simp only [odd,if_false,Option.bind_none,absent]

end Counting.StackMachine.CoreAudit
