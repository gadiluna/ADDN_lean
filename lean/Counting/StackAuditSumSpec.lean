import Counting.StackAuditSum
import Counting.LinearSolver

namespace Counting.StackMachine.AuditSum

/-- The redundant positivity scan does not strengthen the candidate test on
vectors returned by the actual rational-to-natural conversion. -/
theorem positive_of_conversion (values : Array Rat) (natural : Array Nat)
    (converted : Executable.positiveNaturals? values=some natural) :
    RealizabilityCheck.positiveCounts natural.toList=true := by
  obtain ⟨size,positive⟩ := Executable.positiveNaturals_sound values natural converted
  unfold RealizabilityCheck.positiveCounts
  apply List.all_eq_true.mpr
  intro value member
  obtain ⟨index,bound,equal⟩ := List.mem_iff_getElem.mp member
  have ni : index<natural.size := by simpa only [Array.length_toList] using bound
  have vi : index<values.size := by omega
  have p := (positive ⟨index,vi⟩).1
  simp only [Array.getElem?_eq_getElem ni,Option.getD_some] at p
  have equal' : natural[index]=value := by simpa using equal
  simpa only [decide_eq_true_eq,←equal'] using p

theorem accepts_after_conversion (values : Array Rat) (natural : Array Nat)
    (converted : Executable.positiveNaturals? values=some natural) (candidate : Nat) :
    accepts natural.toList candidate=decide (natural.toList.sum=candidate) := by
  simp [accepts,positive_of_conversion values natural converted]

/-- A failed sum comparison really rejects the actual executable continuation. -/
theorem failed_sum_rejects (vista : Executable.Vista) (candidate last anchor : Nat)
    (values : Array Rat) (natural : Array Nat)
    (converted : Executable.positiveNaturals? values=some natural)
    (rejected : accepts natural.toList candidate=false) :
    Executable.auditSuffix? vista candidate last anchor (some values)=none := by
  rw [accepts_after_conversion values natural converted] at rejected
  have different : natural.sum≠candidate := by simpa only [Array.sum_toList,decide_eq_false_iff_not] using rejected
  simp [Executable.auditSuffix?,converted,different]

end Counting.StackMachine.AuditSum
