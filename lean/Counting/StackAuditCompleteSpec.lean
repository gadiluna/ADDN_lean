import Counting.StackAuditCompleteBank

namespace Counting.StackMachine.AuditComplete

def witnessWord (answer : Option Executable.AuditWitness) : List Bool :=
  match answer with
  | none => [false]
  | some witness => true::(Encoding.natural.encode witness.anchor++
      (Encoding.array Encoding.natural).encode witness.weights)

/-- The bounds required by the physical suffix machines follow from the
actual successful prefix. They are never supplied by the local protocol. -/
theorem prefix_success_bounds (vista : Executable.Vista) (leaders candidate last anchor : Nat)
    (found : Executable.auditPrefix? vista leaders candidate last=some anchor) :
    vista.valid=true ∧ anchor≤ last ∧ last+1≤ vista.nodes.size := by
  rw [AuditPrefix.auditPrefix_eq_counts] at found
  cases opening : AuditPrefix.openingAccepted vista leaders candidate last with
  | false => simp [opening] at found
  | true =>
    simp only [opening,ite_true] at found
    have bounds:=AuditPrefix.openingAccepted_bounds vista leaders candidate last opening
    have anchorBound : anchor≤ last := by
      unfold AuditPrefix.countsPrefix? at found
      split at found
      · contradiction
      split at found
      · contradiction
      split at found
      · contradiction
      have member:=List.mem_of_find?_eq_some found
      simp only [List.mem_reverse,List.mem_range] at member
      omega
    exact ⟨bounds.1,anchorBound,bounds.2.2.2.2.2⟩

/-- Exact semantic boundary between the physical suffix and its final
descendant scan, retaining the complete executable witness. -/
theorem suffix_eq (vista : Executable.Vista) (candidate last anchor : Nat)
    (values : Option (Array Rat)) :
    Executable.auditSuffix? vista candidate last anchor values =
      (AuditPostSolver.result vista candidate anchor values).bind (fun weights =>
        if Executable.auditDescendants vista weights anchor last then
          some ⟨anchor,weights⟩ else none) := by
  rw [AuditPostSolver.auditSuffix_after_result]
  simp only [Executable.auditDescendants_eq]
  cases AuditPostSolver.result vista candidate anchor values with
  | none => rfl
  | some weights =>
    simp only [bind,Option.bind_some]
    split <;> simp_all

theorem audit_eq (vista : Executable.Vista) (leaders candidate last : Nat) :
    Executable.audit? vista leaders candidate last =
      (Executable.auditPrefix? vista leaders candidate last).bind (fun anchor =>
        Executable.auditSuffix? vista candidate last anchor
          (Executable.solveLinear? (Executable.levelNodes vista anchor).length
            (Executable.anchorRows vista anchor leaders))) := by
  unfold Executable.audit? Executable.auditPlan
  cases Executable.auditPrefix? vista leaders candidate last <;> rfl

end Counting.StackMachine.AuditComplete
