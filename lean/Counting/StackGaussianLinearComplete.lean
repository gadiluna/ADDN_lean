import Counting.StackGaussianLinearReturn

namespace Counting.StackMachine.GaussianCalls
open Routine GaussianNormalMatrix GaussianBits
set_option backward.isDefEq.respectTransparency false

abbrev complete : Routine 54 := sequence solverPrefix handleSolution

def linearCost (width : Nat) (equations : List Executable.Equation) : Nat :=
  prefixCost (GaussianNormal.inputWord width (equationMatrix width equations)).length
    (Encoding.rationalMatrix.encode (StoredGaussian.augmentedMatrix (Executable.normalSystem width equations))).length+
      1+handleCost width equations

/-- The fixed finite-control composition constructs the normal system,
solves it with a replay-certified stored Gaussian program, and checks all
original equations. No intermediate encoding is inserted for free. -/
theorem complete_executes (width : Nat) (equations : List Executable.Equation)
    (integral : ∀ row column,(augmented (Executable.normalSystem width equations) row column).den=1) :
    ∃ time ≤ linearCost width equations,
      Executes complete (file (GaussianNormal.inputWord width (equationMatrix width equations)) [] [] []) time
        (file [] ((Encoding.optional Encoding.rationalRow).encode (GaussianSolveLinear.result width equations)) [] []) := by
  obtain ⟨prefixTime,prefixBound,a⟩ := prefix_executes width equations integral
  obtain ⟨handleTime,handleBound,b⟩ := handleSolution_executes width equations
  exact ⟨_,by dsimp only [linearCost];omega,a.sequence b⟩

theorem complete_halts (width : Nat) (equations : List Executable.Equation)
    (sized : Executable.RowsSized width equations)
    (coeffIntegral : ∀ r i,(Executable.rowMatrix width equations r i).den=1)
    (rhsIntegral : ∀ r,(Executable.rowRhs equations r).den=1) :
    ∃ time output,time≤ linearCost width equations ∧
      HaltsAt complete.program (GaussianNormal.inputWord width (equationMatrix width equations)) time output ∧
      output.store 1=(Encoding.optional Encoding.rationalRow).encode
        ((Executable.solveLinear? width equations).map Array.toList) := by
  obtain ⟨time,bounded,output,ran,halted,stored⟩ := complete_executes width equations
    (GaussianSolveLinear.normal_integral width equations coeffIntegral rhsIntegral)
  refine ⟨time,output,bounded,⟨?_,halted⟩,?_⟩
  · have initialStore : initial complete.program (GaussianNormal.inputWord width (equationMatrix width equations))=
        ⟨0,file (GaussianNormal.inputWord width (equationMatrix width equations)) [] [] []⟩ := by
      apply congrArg (Config.mk _)
      funext r;fin_cases r <;> simp [file]
    rw [initialStore]
    exact ran
  · rw [stored]
    change (Encoding.optional Encoding.rationalRow).encode (GaussianSolveLinear.result width equations)=_
    rw [GaussianSolveLinear.result_eq_solveLinear width equations sized]

end Counting.StackMachine.GaussianCalls
