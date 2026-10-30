import Counting.StackGaussianNormalComplete
import Counting.StackRoutineIsolateHalt
import Counting.MachineGaussianInputBounds
import Counting.GaussianSolverPolynomial

namespace Counting.StackMachine.GaussianCalls
open Routine GaussianNormalMatrix GaussianBits
open DirectedCounting.VerifiedGaussianAnchorSolver RationalSystem
set_option backward.isDefEq.respectTransparency false

/-- Three cells beyond the largest 53-cell workspace preserve the original
serialized input, a successful solution, and a movement scratch cell. -/
def file (input output original solution : List Bool) : Fin 56 → List Bool :=
  fun r => if r=0 then input else if r=1 then output else if r=53 then original
    else if r=54 then solution else []

def roles (registers : Nat) (fits : registers+2≤53) : Fin (registers+2) ↪ Fin 56 :=
  ⟨fun r=>⟨r.val,by omega⟩,by intro a b equal;exact Fin.ext (congrArg (fun r:Fin 56=>r.val) equal)⟩

theorem lift_executes {registers : Nat} (routine : Routine registers) (fits : registers+2≤53)
    (input output original solution : List Bool) (time : Nat)
    (ran : Executes routine (inputStore registers input) time (outputStore registers output)) :
    Executes (relocate routine (roles registers fits)) (file input [] original solution) time
      (file [] output original solution) := by
  have zero : roles registers fits 0=0 := rfl
  have one : roles registers fits 1=1 := rfl
  apply relocate_executes_frame routine (roles registers fits) _ _ _ _ time _ _ _ ran
  · funext r
    have r53 : roles registers fits r≠53 := by
      intro equal;have value:=congrArg (fun r:Fin 56=>r.val) equal;dsimp [roles] at value;omega
    have r54 : roles registers fits r≠54 := by
      intro equal;have value:=congrArg (fun r:Fin 56=>r.val) equal;dsimp [roles] at value;omega
    have roleZero : roles registers fits r=0 ↔ r=0 := by rw [←zero];exact (roles registers fits).injective.eq_iff
    change file input [] original solution (roles registers fits r)=inputStore registers input r
    simp [file,inputStore,r53,r54,roleZero]
  · intro r
    have r53 : roles registers fits r≠53 := by
      intro equal;have value:=congrArg (fun r:Fin 56=>r.val) equal;dsimp [roles] at value;omega
    have r54 : roles registers fits r≠54 := by
      intro equal;have value:=congrArg (fun r:Fin 56=>r.val) equal;dsimp [roles] at value;omega
    have roleZero : roles registers fits r=0 ↔ r=0 := by rw [←zero];exact (roles registers fits).injective.eq_iff
    have roleOne : roles registers fits r=1 ↔ r=1 := by rw [←one];exact (roles registers fits).injective.eq_iff
    simp only [file,outputStore,r53,r54,if_false,roleZero,roleOne]
    by_cases atZero:r=0
    · subst r;simp
    · simp [atZero]
  · intro r outside
    have notZero : r≠0 := by intro equal;subst r;exact outside 0 zero
    have notOne : r≠1 := by intro equal;subst r;exact outside 1 one
    simp [file,notZero,notOne]

def normalCost (length : Nat) : Nat := 54*(GaussianNormal.normalPolynomialCoefficient*(length+1)^6+length+3)
def squareCost (length : Nat) : Nat := 54*(GaussianBank.solverPolynomialCoefficient*(length+1)^100+length+3)
abbrev normal : Routine 54 := relocate (isolate GaussianNormal.complete) (roles 51 (by decide))
abbrev square : Routine 54 := relocate (isolate GaussianBank.complete) (roles 51 (by decide))

theorem normal_executes (width : Nat) (equations : List Executable.Equation) (original solution : List Bool) :
    ∃ time ≤ normalCost (GaussianNormal.inputWord width (equationMatrix width equations)).length,
      Executes normal (file (GaussianNormal.inputWord width (equationMatrix width equations)) [] original solution) time
        (file [] (Encoding.rationalMatrix.encode (StoredGaussian.augmentedMatrix (Executable.normalSystem width equations)))
          original solution) := by
  obtain ⟨time,bounded,ran⟩ := isolate_halts GaussianNormal.complete _ _ _
    (GaussianNormal.complete_halts_polynomial width equations)
  exact ⟨time,bounded,lift_executes _ _ _ _ original solution _ ran⟩

theorem square_halts {q : Nat} (system : RationalSystem q)
    (integral : ∀ row column,(augmented system row column).den=1) :
    ∃ time output,
      time≤ GaussianBank.solverPolynomialCoefficient*
        ((Encoding.rationalMatrix.encode (StoredGaussian.augmentedMatrix system)).length+1)^100 ∧
      HaltsAt GaussianBank.complete.program (Encoding.rationalMatrix.encode (StoredGaussian.augmentedMatrix system)) time output ∧
      output.store 1=(Encoding.optional Encoding.rationalRow).encode ((StoredGaussian.solve? system).map List.ofFn) := by
  let length := (Encoding.rationalMatrix.encode (StoredGaussian.augmentedMatrix system)).length
  have inputBound (row column) : ((integerEntries system) row column).natAbs≤2^length :=
    (augmented_numerator_lt_input_power system row column).le
  obtain ⟨time,output,bounded,halted,stored⟩ :=
    GaussianBank.complete_halts_integral (integerEntries system) (2^length) inputBound
  rw [integralSystem_integerEntries system integral] at halted stored
  have polynomial := GaussianBank.solverBudget_polynomial q (intermediateBound q (2^length)) length
    (augmented_dimension_le_input system) (intermediateBound_input_le system)
  exact ⟨time,output,bounded.trans polynomial,halted,stored⟩

theorem square_executes {q : Nat} (system : RationalSystem q)
    (integral : ∀ row column,(augmented system row column).den=1) (original solution : List Bool) :
    ∃ time ≤ squareCost (Encoding.rationalMatrix.encode (StoredGaussian.augmentedMatrix system)).length,
      Executes square (file (Encoding.rationalMatrix.encode (StoredGaussian.augmentedMatrix system)) [] original solution) time
        (file [] ((Encoding.optional Encoding.rationalRow).encode ((StoredGaussian.solve? system).map List.ofFn))
          original solution) := by
  obtain ⟨time,bounded,ran⟩ := isolate_halts GaussianBank.complete _ _ _ (square_halts system integral)
  exact ⟨time,bounded,lift_executes _ _ _ _ original solution _ ran⟩

end Counting.StackMachine.GaussianCalls
