import Counting.StackProtocolDecisionPolynomial
import Counting.StackCoreDecisionPolynomial

namespace Counting.StackMachine.ProtocolAdvance
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

def file (input output : List Bool) (saved : Fin 8 → List Bool) : Store 254 :=
  fun r=>if r=0 then input else if r=1 then output
    else if h:r.val<248 then [] else saved ⟨r.val-248,by omega⟩

def roles (extra : Nat) (fits : extra≤ 246) : Fin (extra+2) ↪ Fin 256 :=
  ⟨fun r=>⟨r.val,by omega⟩,by intro a b equal;exact Fin.ext (congrArg (fun r:Fin 256=>r.val) equal)⟩

/-- Lift a complete concrete subprogram while preserving all eight metadata
registers. Every workspace register outside its input and output remains empty. -/
theorem lift_executes {extra : Nat} (routine : Routine extra) (fits : extra≤ 246)
    (input output : List Bool) (saved : Fin 8 → List Bool) (time : Nat)
    (run : Executes routine (inputStore extra input) time (outputStore extra output)) :
    Executes (relocate routine (roles extra fits)) (file input [] saved) time (file [] output saved) := by
  apply relocate_executes_frame routine (roles extra fits) _ _ _ _ time _ _ _ run
  · funext r
    have inside : (roles extra fits r).val<248 := by change r.val<248;omega
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
    have inside : (roles extra fits r).val<248 := by change r.val<248;omega
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

@[noinline] def optimizedDecisionCall : Routine 254 := relocate ProtocolDecision.complete (roles 78 (by decide))
@[noinline] def coreDecisionCall : Routine 254 := relocate CoreDecision.complete (roles 78 (by decide))

end Counting.StackMachine.ProtocolAdvance
