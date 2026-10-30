import Counting.StackProtocolAuditPolynomial
import Counting.StackProtocolVistaComplete

namespace Counting.StackMachine.ProtocolDecision
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

def file (input output : List Bool) (saved : Fin 8 → List Bool) : Store 78 :=
  fun r=>if r=0 then input else if r=1 then output
    else if h:r.val<72 then [] else saved ⟨r.val-72,by omega⟩

def roles (extra : Nat) (fits : extra≤ 70) : Fin (extra+2) ↪ Fin 80 :=
  ⟨fun r=>⟨r.val,by omega⟩,by intro a b equal;exact Fin.ext (congrArg (fun r:Fin 80=>r.val) equal)⟩

/-- Lift a complete concrete subprogram while preserving all eight metadata
registers. Every workspace register outside its input and output remains empty. -/
theorem lift_executes {extra : Nat} (routine : Routine extra) (fits : extra≤ 70)
    (input output : List Bool) (saved : Fin 8 → List Bool) (time : Nat)
    (run : Executes routine (inputStore extra input) time (outputStore extra output)) :
    Executes (relocate routine (roles extra fits)) (file input [] saved) time (file [] output saved) := by
  apply relocate_executes_frame routine (roles extra fits) _ _ _ _ time _ _ _ run
  · funext r
    have inside : (roles extra fits r).val<72 := by change r.val<72;omega
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
    have inside : (roles extra fits r).val<72 := by change r.val<72;omega
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

abbrev vistaCall : Routine 78 := relocate ProtocolVista.complete (roles 50 (by decide))
abbrev scheduledAuditCall : Routine 78 := relocate ProtocolAudit.complete (roles 70 (by decide))

end Counting.StackMachine.ProtocolDecision
