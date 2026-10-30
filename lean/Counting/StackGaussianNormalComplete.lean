import Counting.StackGaussianNormalBounds
import Counting.StackGaussianNormalInput

namespace Counting.StackMachine.GaussianNormal
open Routine GaussianNormalMatrix
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000

abbrev complete : Routine 51 := sequence prepareInput generate

def normalBudget (width size : Nat) : Nat := 2200*(size+2*width+3)^3+1+generatorBudget width size

theorem complete_halts (width : Nat) (equations : List Executable.Equation) :
    ∃ time output,
      time ≤ normalBudget width (Encoding.rationalMatrix.encode (equationMatrix width equations)).length ∧
      HaltsAt complete.program (inputWord width (equationMatrix width equations)) time output ∧
      output.store 1=Encoding.rationalMatrix.encode (StoredGaussian.augmentedMatrix (Executable.normalSystem width equations)) := by
  obtain ⟨prepareTime,prepareBound,a⟩ := prepareInput_executes width equations
  obtain ⟨generateTime,generateBound,b⟩ := generate_bounded width equations
  obtain ⟨output,ran,halted,stored⟩ := a.sequence b
  refine ⟨prepareTime+1+generateTime,output,by dsimp [normalBudget];omega,⟨?_,halted⟩,?_⟩
  · have initialStore : initial complete.program (inputWord width (equationMatrix width equations))=
        ⟨0,inputBank (inputWord width (equationMatrix width equations)) [] [] [] [] [] [] [] []⟩ := by
      apply congrArg (Config.mk _)
      funext r;fin_cases r <;> simp [inputBank]
    rw [initialStore]
    exact ran
  · rw [stored]
    simp [outputStore]

def normalPolynomialCoefficient : Nat := 1000000000000000000

theorem normalBudget_polynomial (width size length : Nat) (widthBound : width≤length) (sizeBound : size≤length) :
    normalBudget width size≤ normalPolynomialCoefficient*(length+1)^6 := by
  have monotone : normalBudget width size≤ normalBudget length length := by
    dsimp [normalBudget,generatorBudget,rowBudget,columnBudget,normalStreamBound,normalRowBound]
    gcongr
  apply monotone.trans
  dsimp [normalBudget,generatorBudget,rowBudget,columnBudget,normalStreamBound,normalRowBound,normalPolynomialCoefficient]
  ring_nf
  omega

theorem complete_halts_polynomial (width : Nat) (equations : List Executable.Equation) :
    ∃ time output,
      time ≤ normalPolynomialCoefficient*((inputWord width (equationMatrix width equations)).length+1)^6 ∧
      HaltsAt complete.program (inputWord width (equationMatrix width equations)) time output ∧
      output.store 1=Encoding.rationalMatrix.encode (StoredGaussian.augmentedMatrix (Executable.normalSystem width equations)) := by
  obtain ⟨time,output,bounded,ran,stored⟩ := complete_halts width equations
  have length : (inputWord width (equationMatrix width equations)).length=
      2*width+1+(Encoding.rationalMatrix.encode (equationMatrix width equations)).length := by
    simp [inputWord,Encoding.frame_length]
  exact ⟨time,output,bounded.trans (normalBudget_polynomial _ _ _ (by omega) (by omega)),ran,stored⟩

end Counting.StackMachine.GaussianNormal
