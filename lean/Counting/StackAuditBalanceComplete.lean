import Counting.StackAuditBalanceFinish

namespace Counting.StackMachine.AuditBalance
open Routine
set_option backward.isDefEq.respectTransparency false

abbrev completeBalance : Routine 48 := sequence prepareBalanceInput
  (sequence prepareBalanceRounds (sequence roundsLoop finishBalance))

def balanceBudget (anchor : Nat) (vista : Executable.Vista) (weights : Array Nat) : Nat :=
  3000*((balanceInputWord anchor vista weights).length+1)^3+
    1200*(vista.nodes.size+anchor.size+1)^3+roundsBudget vista weights 0 (anchor-1)+
    balanceCleanupBudget anchor vista weights+3

/-- Canonical input to Boolean output, with all fifty registers accounted
for. The logical validity and weight-shape premises justify the mass-sum parser. -/
theorem completeBalance_executes (anchor : Nat) (vista : Executable.Vista) (weights : Array Nat)
    (fits : anchor ≤ vista.nodes.size) (valid : vista.valid=true) (length : weights.size=vista.nodes.size) :
    ∃ time ≤ balanceBudget anchor vista weights,
      Executes completeBalance (inputStore 48 (balanceInputWord anchor vista weights)) time
        (outputStore 48 [Executable.auditBalance vista weights anchor]) := by
  obtain ⟨inputTime,inputBound,a⟩:=prepareBalanceInput_executes anchor vista weights
  obtain ⟨roundTime,roundBound,b⟩:=prepareBalanceRounds_setup anchor vista weights fits
  obtain ⟨bodyTime,bodyBound,c⟩:=balancePrepared_executes anchor vista weights valid length
  obtain ⟨finishTime,finishBound,d⟩:=finishBalance_executes anchor vista weights
  have initial : balanceInputFile (balanceInputWord anchor vista weights) [] [] []=
      inputStore 48 (balanceInputWord anchor vista weights) := by
    funext r
    fin_cases r <;> simp [balanceInputFile,inputStore]
  rw [initial] at a
  refine ⟨_,?_,a.sequence (b.sequence (c.sequence d))⟩
  dsimp only [balanceBudget]
  omega

end Counting.StackMachine.AuditBalance
