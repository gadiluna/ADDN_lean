import Counting.StackGaussianCanonicalCalls
import Counting.GaussianSolveLinearSpec

namespace Counting.StackMachine.GaussianCalls
open Routine GaussianNormalMatrix GaussianBits
open DirectedCounting.VerifiedGaussianAnchorSolver RationalSystem
set_option backward.isDefEq.respectTransparency false

abbrev saveInput : Routine 54 := ofProgram (ListPrograms.copyProgram 53 0 53 55)
abbrev forward : Routine 54 := move 53 1 0 55
abbrev solverPrefix : Routine 54 := sequence saveInput (sequence normal (sequence forward square))

theorem saveInput_executes (input : List Bool) :
    Executes saveInput (file input [] [] []) (5*input.length+2) (file input [] input []) := by
  have ran := copy_executes 53 (0:Fin 56) 53 55 (by decide) (by decide) (by decide) (file input [] [] []) rfl
  have stored : Function.update (file input [] [] []) 53 (input++[])=file input [] input [] := by
    funext r;fin_cases r <;> simp [file]
  change Executes _ _ (5*input.length+2) (Function.update (file input [] [] []) 53 (input++[])) at ran
  rw [stored] at ran
  exact ran

theorem forward_executes (value original solution : List Bool) :
    Executes forward (file [] value original solution) (6*value.length+4) (file value [] original solution) := by
  have ran := move_executes 53 (1:Fin 56) 0 55 (by decide) (by decide) (by decide) (file [] value original solution) rfl
  have stored : Function.update (Function.update (file [] value original solution) 0 (value++[])) 1 []=
      file value [] original solution := by
    funext r;fin_cases r <;> simp [file]
  change Executes _ _ (6*value.length+4)
    (Function.update (Function.update (file [] value original solution) 0 (value++[])) 1 []) at ran
  rw [stored] at ran
  exact ran

def prefixCost (inputLength normalLength : Nat) : Nat :=
  5*inputLength+normalCost inputLength+6*normalLength+squareCost normalLength+9

theorem prefix_executes (width : Nat) (equations : List Executable.Equation)
    (integral : ∀ row column,(augmented (Executable.normalSystem width equations) row column).den=1) :
    ∃ time ≤ prefixCost (GaussianNormal.inputWord width (equationMatrix width equations)).length
        (Encoding.rationalMatrix.encode (StoredGaussian.augmentedMatrix (Executable.normalSystem width equations))).length,
      Executes solverPrefix (file (GaussianNormal.inputWord width (equationMatrix width equations)) [] [] []) time
        (file [] ((Encoding.optional Encoding.rationalRow).encode
          ((StoredGaussian.solve? (Executable.normalSystem width equations)).map List.ofFn))
          (GaussianNormal.inputWord width (equationMatrix width equations)) []) := by
  let input := GaussianNormal.inputWord width (equationMatrix width equations)
  let normalWord := Encoding.rationalMatrix.encode (StoredGaussian.augmentedMatrix (Executable.normalSystem width equations))
  have a := saveInput_executes input
  obtain ⟨normalTime,normalBound,b⟩ := normal_executes width equations input []
  have c := forward_executes normalWord input []
  obtain ⟨squareTime,squareBound,d⟩ := square_executes (Executable.normalSystem width equations) integral input []
  refine ⟨_,?_,a.sequence (b.sequence (c.sequence d))⟩
  dsimp only [prefixCost,input,normalWord]
  omega

end Counting.StackMachine.GaussianCalls
