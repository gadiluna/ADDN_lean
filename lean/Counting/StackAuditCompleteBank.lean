import Counting.StackAuditPrefixComplete
import Counting.StackAnchorSolve
import Counting.StackAuditPostSolverPolynomial
import Counting.StackAuditDescendantComplete

namespace Counting.StackMachine.AuditComplete
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

def file (input output : List Bool) (saved : Fin 8 → List Bool) : Store 62 :=
  fun r=>if r=0 then input else if r=1 then output
    else if h:r.val<56 then [] else saved ⟨r.val-56,by omega⟩

def roles (extra : Nat) (fits : extra≤ 54) : Fin (extra+2) ↪ Fin 64 :=
  ⟨fun r=>⟨r.val,by omega⟩,by intro a b equal;exact Fin.ext (congrArg (fun r:Fin 64=>r.val) equal)⟩

/-- Lift a complete concrete subprogram while preserving all eight metadata
registers. Every workspace register outside its input and output remains empty. -/
theorem lift_executes {extra : Nat} (routine : Routine extra) (fits : extra≤ 54)
    (input output : List Bool) (saved : Fin 8 → List Bool) (time : Nat)
    (run : Executes routine (inputStore extra input) time (outputStore extra output)) :
    Executes (relocate routine (roles extra fits)) (file input [] saved) time (file [] output saved) := by
  apply relocate_executes_frame routine (roles extra fits) _ _ _ _ time _ _ _ run
  · funext r
    have inside : (roles extra fits r).val<56 := by change r.val<56;omega
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
    have inside : (roles extra fits r).val<56 := by change r.val<56;omega
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

abbrev prefixCall : Routine 62 := relocate AuditPrefix.complete (roles 50 (by decide))
abbrev solverCall : Routine 62 := relocate AnchorSolve.routine (roles 54 (by decide))
abbrev postSolverCall : Routine 62 := relocate AuditPostSolver.complete (roles 54 (by decide))
abbrev descendantCall : Routine 62 := relocate AuditDescendant.complete (roles 46 (by decide))

theorem prefixCall_executes (vista : Executable.Vista) (leaders candidate last : Nat) (saved : Fin 8 → List Bool) :
    ∃ time ≤ AuditPrefix.completeCoefficient*((AuditPrefix.inputWord vista leaders candidate last).length+1)^7,
      Executes prefixCall (file (AuditPrefix.inputWord vista leaders candidate last) [] saved) time
        (file [] (Encoding.optionalNatural.encode (Executable.auditPrefix? vista leaders candidate last)) saved) := by
  obtain ⟨time,bounded,run⟩:=AuditPrefix.complete_executes vista leaders candidate last
  exact ⟨time,bounded,lift_executes _ _ _ _ _ _ run⟩

theorem solverCall_executes (vista : Executable.Vista) (anchor leaders : Nat) (saved : Fin 8 → List Bool) :
    ∃ time ≤ AnchorSolve.polynomialCoefficient*((AnchorMatrix.inputWord anchor leaders vista).length+1)^4500,
      Executes solverCall (file (AnchorMatrix.inputWord anchor leaders vista) [] saved) time
        (file [] (AnchorSolve.resultWord vista anchor leaders) saved) := by
  obtain ⟨time,bounded,run⟩:=AnchorSolve.routine_executes vista anchor leaders
  have input : GaussianCalls.file (AnchorMatrix.inputWord anchor leaders vista) [] [] []=
      inputStore 54 (AnchorMatrix.inputWord anchor leaders vista) := by
    funext r;fin_cases r <;> simp [GaussianCalls.file,inputStore]
  have output : GaussianCalls.file [] (AnchorSolve.resultWord vista anchor leaders) [] []=
      outputStore 54 (AnchorSolve.resultWord vista anchor leaders) := by
    funext r;fin_cases r <;> simp [GaussianCalls.file,outputStore]
  rw [input,output] at run
  exact ⟨time,bounded,lift_executes _ _ _ _ _ _ run⟩

theorem postSolverCall_executes (vista : Executable.Vista) (candidate anchor : Nat)
    (values : Option (Array Rat)) (fits : anchor≤ vista.nodes.size) (valid : vista.valid=true)
    (saved : Fin 8 → List Bool) :
    ∃ time ≤ AuditPostSolver.completeCoefficient*((AuditPostSolver.inputWord vista candidate anchor values).length+1)^51,
      Executes postSolverCall (file (AuditPostSolver.inputWord vista candidate anchor values) [] saved) time
        (file [] (AuditPostSolver.outputWord vista candidate anchor values) saved) := by
  obtain ⟨time,bounded,run⟩:=AuditPostSolver.complete_polynomial vista candidate anchor values fits valid
  exact ⟨time,bounded,lift_executes _ _ _ _ _ _ run⟩

theorem descendantCall_executes (vista : Executable.Vista) (weights : Array Nat) (anchor last : Nat)
    (fits : last≤ vista.nodes.size) (saved : Fin 8 → List Bool) :
    ∃ time≤ AuditDescendant.completeCoefficient*((AuditDescendant.completeInputWord vista weights anchor last).length+1)^7,
      Executes descendantCall (file (AuditDescendant.completeInputWord vista weights anchor last) [] saved) time
        (file [] [Executable.auditDescendants vista weights anchor last] saved) := by
  obtain ⟨time,bounded,run⟩:=AuditDescendant.complete_executes vista weights anchor last fits
  exact ⟨time,bounded,lift_executes _ _ _ _ _ _ run⟩

end Counting.StackMachine.AuditComplete
