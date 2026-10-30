import Counting.StackGaussianBank
import Counting.StackPositiveNaturalsCall
import Counting.StackRationalInverse
import Counting.StackRationalNegation

namespace Counting.StackMachine.GaussianBank
open Routine
set_option backward.isDefEq.respectTransparency false

def scalarRoles : Fin 20 ↪ Fin 52 := ⟨fun r => r.castLE (by decide),by
  intro a b equal
  exact Fin.ext (congrArg (fun r : Fin 52 => r.val) equal)⟩

def scalarStage (matrix input output first second : List Bool) (saved : Fin 10 → List Bool) : Fin 52 → List Bool :=
  bank (MatrixAxpy.file input matrix first second output [] [] [] []) saved

abbrev scalarCall (routine : Routine 14) : Routine 50 :=
  relocate (PositiveNaturalsCall.invoke routine) scalarRoles
abbrev scalarApply (routine : Routine 14) : Routine 50 :=
  sequence (scalarCall routine) (sequence (clear 0) (move 49 1 0 2))

/-- A scalar machine is actually called, its old input erased, and its new
value moved back to the factor register. Every other live field survives. -/
theorem scalarApply_executes (routine : Routine 14) (function : List Bool → List Bool)
    (bound : Nat → Nat) (computes : ComputesIn routine.program function bound)
    (matrix input first second : List Bool) (saved : Fin 10 → List Bool) :
    ∃ time ≤ 50*(bound input.length+input.length+3),
      Executes (scalarApply routine) (ready matrix input first second saved) time
        (ready matrix (function input) first second saved) := by
  obtain ⟨time,bounded,ran⟩ := PositiveNaturalsCall.invoke_executes routine function bound computes input
  have called : Executes (scalarCall routine) (ready matrix input first second saved) time
      (scalarStage matrix input (function input) first second saved) := by
    apply relocate_executes_frame (PositiveNaturalsCall.invoke routine) scalarRoles _ _ _ _ time _ _ _ ran
    · funext r;fin_cases r <;> simp [ready,bank,scalarRoles,MatrixAxpy.file,RowAxpy.file,PositiveNaturalsCall.file]
    · intro r;fin_cases r <;> simp [scalarStage,bank,scalarRoles,MatrixAxpy.file,RowAxpy.file,PositiveNaturalsCall.file]
    · intro r outside
      have result := outside 1
      fin_cases r <;> simp_all [scalarStage,ready,bank,scalarRoles,MatrixAxpy.file,RowAxpy.file]
  have erased := clear_executes (0 : Fin 52) (scalarStage matrix input (function input) first second saved)
  have erasedStore : Function.update (scalarStage matrix input (function input) first second saved) 0 []=
      scalarStage matrix [] (function input) first second saved := by
    funext r;fin_cases r <;> simp [scalarStage,bank,MatrixAxpy.file,RowAxpy.file]
  rw [erasedStore] at erased
  change Executes _ _ (input.length+1) _ at erased
  have moved := move_executes 49 (1 : Fin 52) 0 2 (by decide) (by decide) (by decide)
    (scalarStage matrix [] (function input) first second saved) rfl
  have movedStore : Function.update (Function.update (scalarStage matrix [] (function input) first second saved) 0
      (function input++[])) 1 []=ready matrix (function input) first second saved := by
    funext r;fin_cases r <;> simp [scalarStage,ready,bank,MatrixAxpy.file,RowAxpy.file]
  change Executes _ _ (6*(function input).length+4)
    (Function.update (Function.update (scalarStage matrix [] (function input) first second saved) 0 (function input++[])) 1 []) at moved
  rw [movedStore] at moved
  have outputBound := computed_length_le routine function bound computes input
  exact ⟨_,by omega,called.sequence (erased.sequence moved)⟩

abbrev inverse : Routine 50 := scalarApply RationalArithmetic.inverseRoutine
abbrev negate : Routine 50 := scalarApply RationalArithmetic.negationRoutine

theorem inverse_executes (value : Rat) (matrix first second : List Bool) (saved : Fin 10 → List Bool) :
    ∃ time ≤ 100000000*((Encoding.rational.encode value).length+1)^3,
      Executes inverse (ready matrix (Encoding.rational.encode value) first second saved) time
        (ready matrix (Encoding.rational.encode value⁻¹) first second saved) := by
  obtain ⟨time,bounded,ran⟩ := scalarApply_executes RationalArithmetic.inverseRoutine _ _
    RationalArithmetic.inverse_computes matrix (Encoding.rational.encode value) first second saved
  rw [RationalArithmetic.inverseFunction_rational] at ran
  have linear := Nat.le_self_pow (by decide : 3≠0) ((Encoding.rational.encode value).length+1)
  have positive := Nat.one_le_pow' 3 (Encoding.rational.encode value).length
  refine ⟨time,?_,ran⟩
  simp only [Complexity.polynomial] at bounded
  omega

theorem negate_executes (value : Rat) (matrix first second : List Bool) (saved : Fin 10 → List Bool) :
    ∃ time ≤ 100000000*((Encoding.rational.encode value).length+1)^3,
      Executes negate (ready matrix (Encoding.rational.encode value) first second saved) time
        (ready matrix (Encoding.rational.encode (-value)) first second saved) := by
  obtain ⟨time,bounded,ran⟩ := scalarApply_executes RationalArithmetic.negationRoutine _ _
    RationalArithmetic.negation_computes matrix (Encoding.rational.encode value) first second saved
  rw [RationalArithmetic.negationFunction_rational] at ran
  have linear := Nat.le_self_pow (by decide : 3≠0) ((Encoding.rational.encode value).length+1)
  have positive := Nat.one_le_pow' 3 (Encoding.rational.encode value).length
  refine ⟨time,?_,ran⟩
  simp only [Complexity.polynomial] at bounded
  omega

end Counting.StackMachine.GaussianBank
