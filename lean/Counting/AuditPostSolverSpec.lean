import Counting.StackAuditCandidate
import Counting.AuditBalanceSuffix

namespace Counting.StackMachine.AuditPostSolver

def result (vista : Executable.Vista) (candidate anchor : Nat)
    (values : Option (Array Rat)) : Option (Array Nat) := do
  let natural←AuditCandidate.result values candidate
  let weights:=Executable.propagateWeights vista anchor natural
  if Executable.auditBalance vista weights anchor then some weights else none

/-- Factor the actual suffix at the last remaining descendant test.
The intermediate result contains exactly the propagated weights, or None. -/
theorem auditSuffix_after_result (vista : Executable.Vista) (candidate last anchor : Nat)
    (values : Option (Array Rat)) :
    Executable.auditSuffix? vista candidate last anchor values = do
      let weights←result vista candidate anchor values
      if !(Executable.levelNodes vista anchor).all (fun v=>
        ((Executable.levelNodes vista last).filter (fun descendant=>
          Executable.ascend vista (last-anchor) descendant==some v)).length ≤
          (weights[v]?.getD 0)) then none else
        return ⟨anchor,weights⟩ := by
  cases values with
  | none=>rfl
  | some values=>
    cases converted : Executable.positiveNaturals? values with
    | none=>simp [Executable.auditSuffix?,result,AuditCandidate.result,AuditPositive.result,converted]
    | some natural=>
      by_cases sum : natural.sum=candidate
      · by_cases balance : Executable.auditBalance vista (Executable.propagateWeights vista anchor natural) anchor=true
        · simp [Executable.auditSuffix?,result,AuditCandidate.result,AuditPositive.result,
            converted,sum,←Executable.auditBalance_eq,balance]
        · simp [Executable.auditSuffix?,result,AuditCandidate.result,AuditPositive.result,
            converted,sum,←Executable.auditBalance_eq,balance]
      · simp [Executable.auditSuffix?,result,AuditCandidate.result,AuditPositive.result,converted,sum]

theorem failure_rejects (vista : Executable.Vista) (candidate last anchor : Nat)
    (values : Option (Array Rat)) (failure : result vista candidate anchor values=none) :
    Executable.auditSuffix? vista candidate last anchor values=none := by
  rw [auditSuffix_after_result,failure]
  rfl

end Counting.StackMachine.AuditPostSolver
