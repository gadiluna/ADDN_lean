import Counting.StackAuditBalancePrepareRounds
import Counting.StackAuditBalanceRounds

namespace Counting.StackMachine.AuditBalance
open Routine RealizabilityCheck
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

def balanceSaved (anchor : Nat) (vista : Executable.Vista) : Fin 8 → List Bool :=
  ![Encoding.sequence Encoding.node vista.nodes.toList++Encoding.natural.encode vista.bottom,
    [],[],[],[],[],List.replicate (anchor-1) true,List.replicate vista.nodes.size true]

def balanceReadyFile (anchor : Nat) (vista : Executable.Vista) (weights : Array Nat) : Store 48 :=
  bankFile (Encoding.vista.encode vista) ((Encoding.array Encoding.natural).encode weights)
    (1:Nat).bits [] [true] (balanceSaved anchor vista)

def balanceDoneFile (anchor : Nat) (vista : Executable.Vista) (weights : Array Nat) : Store 48 :=
  bankFile (Encoding.vista.encode vista) ((Encoding.array Encoding.natural).encode weights)
    (anchor-1+1).bits [] [Executable.auditBalance vista weights anchor]
    (roundsSaved (balanceSaved anchor vista) 0 (anchor-1))

theorem prepareBalanceRounds_setup (anchor : Nat) (vista : Executable.Vista) (weights : Array Nat)
    (fits : anchor ≤ vista.nodes.size) :
    ∃ time ≤ 1200*(vista.nodes.size+anchor.size+1)^3,
      Executes prepareBalanceRounds (balanceSetupFile anchor vista weights) time
        (balanceReadyFile anchor vista weights) := by
  obtain ⟨time,bounded,run⟩:=prepareBalanceRounds_executes (balanceSetupFile anchor vista weights) anchor vista.nodes.size
    (by simp [balanceSetupFile,balanceInputFile]) (by simp [balanceSetupFile])
    (by intro i member;fin_cases i <;> simp_all [balanceSetupFile,balanceInputFile])
  rw [Nat.min_eq_left fits] at run
  have result : Function.update (Function.update (Function.update (balanceSetupFile anchor vista weights) 36 []) 48
        (List.replicate (anchor-1) true)) 22 [true]=balanceReadyFile anchor vista weights := by
    funext r
    fin_cases r <;> simp [balanceSetupFile,balanceInputFile,balanceReadyFile,bankFile,massFile,balanceSaved]
  rw [result] at run
  exact ⟨time,bounded,run⟩

/-- The prepared binary computation is exactly the balance condition in
the executable audit, including anchor zero and one. -/
theorem balancePrepared_executes (anchor : Nat) (vista : Executable.Vista) (weights : Array Nat)
    (valid : vista.valid=true) (length : weights.size=vista.nodes.size) :
    ∃ time ≤ roundsBudget vista weights 0 (anchor-1),
      Executes roundsLoop (balanceReadyFile anchor vista weights) time
        (balanceDoneFile anchor vista weights) := by
  obtain ⟨time,bounded,run⟩:=roundsLoop_executes vista weights valid length 0 (anchor-1) true []
    (balanceSaved anchor vista) rfl rfl rfl rfl rfl rfl rfl rfl
  refine ⟨time,bounded,?_⟩
  simpa only [balanceReadyFile,balanceDoneFile,Nat.zero_add,Bool.true_and,
    Executable.auditBalanceRounds_anchor] using run

end Counting.StackMachine.AuditBalance
