import Counting.StackAuditCandidate
import Counting.StackAuditPropagationPolynomial
import Counting.StackAuditBalancePolynomial

namespace Counting.StackMachine.AuditPostSolver
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

def file (input output : List Bool) (saved : Fin 6 → List Bool) : Store 54 :=
  fun r=>if r=0 then input else if r=1 then output
    else if h:r.val<50 then [] else saved ⟨r.val-50,by omega⟩

def roles (extra : Nat) (fits : extra≤48) : Fin (extra+2) ↪ Fin 56 :=
  ⟨fun r=>⟨r.val,by omega⟩,by intro a b equal;exact Fin.ext (congrArg (fun r:Fin 56=>r.val) equal)⟩

/-- Lift a complete concrete subprogram while preserving all six metadata
registers. Every workspace register outside its input and output remains empty. -/
theorem lift_executes {extra : Nat} (routine : Routine extra) (fits : extra≤48)
    (input output : List Bool) (saved : Fin 6 → List Bool) (time : Nat)
    (run : Executes routine (inputStore extra input) time (outputStore extra output)) :
    Executes (relocate routine (roles extra fits)) (file input [] saved) time (file [] output saved) := by
  apply relocate_executes_frame routine (roles extra fits) _ _ _ _ time _ _ _ run
  · funext r
    have inside : (roles extra fits r).val<50 := by change r.val<50;omega
    have zero : roles extra fits r=0 ↔ r=0 := by
      have fixed : roles extra fits 0=0 := by apply Fin.ext;simp [roles]
      constructor
      · intro equal;exact (roles extra fits).injective (equal.trans fixed.symm)
      · rintro rfl;exact fixed
    have one : roles extra fits r=1 ↔ r=1 := by
      have fixed : roles extra fits 1=1 := by apply Fin.ext;simp [roles]
      constructor
      · intro equal;exact (roles extra fits).injective (equal.trans fixed.symm)
      · rintro rfl;exact fixed
    simp [file,inputStore,zero,one,inside]
  · intro r
    have inside : (roles extra fits r).val<50 := by change r.val<50;omega
    have zero : roles extra fits r=0 ↔ r=0 := by
      have fixed : roles extra fits 0=0 := by apply Fin.ext;simp [roles]
      constructor
      · intro equal;exact (roles extra fits).injective (equal.trans fixed.symm)
      · rintro rfl;exact fixed
    have one : roles extra fits r=1 ↔ r=1 := by
      have fixed : roles extra fits 1=1 := by apply Fin.ext;simp [roles]
      constructor
      · intro equal;exact (roles extra fits).injective (equal.trans fixed.symm)
      · rintro rfl;exact fixed
    simp [file,outputStore,zero,one,inside]
    intro zero one
    have equal := congrArg Fin.val (zero.symm.trans one)
    simp only [Fin.val_zero,Fin.val_one] at equal
    omega
  · intro r outside
    have r0 : r≠0 := by
      intro equal
      subst r
      exact outside 0 rfl
    have r1 : r≠1 := by
      intro equal
      subst r
      exact outside 1 rfl
    simp [file,r0,r1]

abbrev candidateCall : Routine 54 := relocate AuditCandidate.complete (roles 34 (by decide))
abbrev propagationCall : Routine 54 := relocate AuditPropagation.completePropagation (roles 42 (by decide))
abbrev balanceCall : Routine 54 := relocate AuditBalance.completeBalance (roles 48 (by decide))

theorem candidateCall_executes (values : Option (Array Rat)) (candidate : Nat) (saved : Fin 6 → List Bool) :
    ∃ time ≤ 500000*((AuditCandidate.inputWord values candidate).length+1)^3,
      Executes candidateCall (file (AuditCandidate.inputWord values candidate) [] saved) time
        (file [] (AuditCandidate.outputWord values candidate) saved) := by
  obtain ⟨time,bounded,run⟩:=AuditCandidate.complete_executes values candidate
  exact ⟨time,bounded,lift_executes _ _ _ _ _ _ run⟩

theorem propagationCall_executes (anchor : Nat) (vista : Executable.Vista) (values : Array Nat)
    (fits : anchor≤vista.nodes.size) (saved : Fin 6 → List Bool) :
    ∃ time ≤ AuditPropagation.propagationCoefficient*((AuditPropagation.propagationInputWord anchor vista values).length+1)^32,
      Executes propagationCall (file (AuditPropagation.propagationInputWord anchor vista values) [] saved) time
        (file [] (AuditPropagation.propagationOutputWord anchor vista values) saved) := by
  obtain ⟨time,bounded,run⟩:=AuditPropagation.completePropagation_polynomial anchor vista values fits
  exact ⟨time,bounded,lift_executes _ _ _ _ _ _ run⟩

theorem balanceCall_executes (anchor : Nat) (vista : Executable.Vista) (values : Array Nat)
    (fits : anchor≤vista.nodes.size) (valid : vista.valid=true) (length : values.size=vista.nodes.size)
    (saved : Fin 6 → List Bool) :
    ∃ time ≤ AuditBalance.balanceCoefficient*((AuditBalance.balanceInputWord anchor vista values).length+1)^17,
      Executes balanceCall (file (AuditBalance.balanceInputWord anchor vista values) [] saved) time
        (file [] [Executable.auditBalance vista values anchor] saved) := by
  obtain ⟨time,bounded,run⟩:=AuditBalance.completeBalance_polynomial anchor vista values fits valid length
  exact ⟨time,bounded,lift_executes _ _ _ _ _ _ run⟩

end Counting.StackMachine.AuditPostSolver
