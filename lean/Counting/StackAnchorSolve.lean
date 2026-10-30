import Counting.StackAnchorMatrix
import Counting.GaussianLinearPolynomial
import Counting.GaussianAnchorDomain

namespace Counting.StackMachine.AnchorSolve
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 131072
set_option exponentiation.threshold 10000

private theorem product_power (c b s : Nat) :
    c*(b*s^3)^1500=(c*b^1500)*s^4500 := by
  rw [mul_pow,←pow_mul]
  simp only [Nat.mul_assoc]

def solverFactor : Nat := GaussianCalls.linearPolynomialCoefficient*10008^1500
def polynomialCoefficient : Nat := 7001000000+solverFactor

abbrev routine : Routine 54 := sequence
  (relocate AnchorMatrix.complete (GaussianCalls.roles 48 (by decide)))
  (sequence (move 53 1 0 55) GaussianCalls.complete)

def resultWord (vista : Executable.Vista) (anchor leaders : Nat) : List Bool :=
  (Encoding.optional Encoding.rationalRow).encode
    ((Executable.solveLinear? (Executable.levelNodes vista anchor).length
      (Executable.anchorRows vista anchor leaders)).map Array.toList)

/-- The real DAG-to-equations transducer feeds the real rectangular solver.
Even the transfer between their workspaces is an executed, charged copy. -/
theorem routine_executes (vista : Executable.Vista) (anchor leaders : Nat) :
    ∃ time ≤ polynomialCoefficient*((AnchorMatrix.inputWord anchor leaders vista).length+1)^4500,
      Executes routine (GaussianCalls.file (AnchorMatrix.inputWord anchor leaders vista) [] [] []) time
        (GaussianCalls.file [] (resultWord vista anchor leaders) [] []) := by
  obtain ⟨buildTime,buildBound,building⟩ := AnchorMatrix.complete_executes anchor leaders vista
  let input := AnchorMatrix.inputWord anchor leaders vista
  let intermediate := AnchorMatrix.outputWord anchor leaders vista
  have buildingAs : Executes AnchorMatrix.complete (inputStore 48 input) buildTime (outputStore 48 intermediate) := by
    convert building using 1
    · funext r;fin_cases r <;> simp [inputStore,AnchorMatrix.inputFile,input]
    · funext r;fin_cases r <;> simp [outputStore,AnchorMatrix.outputFile,intermediate]
  have a := GaussianCalls.lift_executes AnchorMatrix.complete (by decide) input intermediate [] [] buildTime buildingAs
  have b := move_executes 53 (1:Fin 56) 0 55 (by decide) (by decide) (by decide)
    (GaussianCalls.file [] intermediate [] []) rfl
  have bs : Function.update (Function.update (GaussianCalls.file [] intermediate [] []) 0 (intermediate++[])) 1 []=
      GaussianCalls.file intermediate [] [] [] := by
    funext r;fin_cases r <;> simp [GaussianCalls.file]
  change Executes _ _ (6*intermediate.length+4)
    (Function.update (Function.update (GaussianCalls.file [] intermediate [] []) 0 (intermediate++[])) 1 []) at b
  rw [bs] at b
  let width := (Executable.levelNodes vista anchor).length
  let equations := Executable.anchorRows vista anchor leaders
  obtain ⟨coeff,rhs⟩ := Executable.anchorRows_integral vista anchor leaders width
  have integral := GaussianSolveLinear.normal_integral width equations coeff rhs
  obtain ⟨solveTime,solveBound,c⟩ := GaussianCalls.complete_executes width equations integral
  have result : GaussianSolveLinear.result width equations=
      (Executable.solveLinear? width equations).map Array.toList :=
    GaussianSolveLinear.result_eq_solveLinear width equations (Executable.anchorRows_sized vista anchor leaders)
  rw [result] at c
  have composed := a.sequence (b.sequence c)
  refine ⟨_,?_,composed⟩
  let size := input.length+1
  have one : 1 ≤ size := by dsimp only [size];omega
  have outputBound := AnchorMatrix.outputWord_length anchor leaders vista
  change intermediate.length ≤ 10007*size^3 at outputBound
  have powerPositive : 1 ≤ size^3 := Nat.one_le_pow _ _ one
  have outputBase : intermediate.length+1 ≤ 10008*size^3 := by omega
  have solvePolynomial := GaussianCalls.linearCost_polynomial width equations integral
  change GaussianCalls.linearCost width equations ≤
    GaussianCalls.linearPolynomialCoefficient*(intermediate.length+1)^1500 at solvePolynomial
  have solveRaised := solveBound.trans (solvePolynomial.trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left outputBase 1500)))
  have solveFinal : solveTime ≤ solverFactor*size^4500 := by
    rw [product_power] at solveRaised
    exact solveRaised
  have cubic : size^3 ≤ size^4500 := Nat.pow_le_pow_right one (by decide)
  have sixth : size^6 ≤ size^4500 := Nat.pow_le_pow_right one (by decide)
  have positive : 1 ≤ size^4500 := Nat.one_le_pow _ _ one
  change buildTime ≤ 7000000000*size^6 at buildBound
  change _ ≤ polynomialCoefficient*size^4500
  unfold polynomialCoefficient
  rw [Nat.add_mul]
  omega

theorem routine_halts (vista : Executable.Vista) (anchor leaders : Nat) :
    ∃ steps output,
      steps ≤ polynomialCoefficient*((AnchorMatrix.inputWord anchor leaders vista).length+1)^4500 ∧
      HaltsAt routine.program (AnchorMatrix.inputWord anchor leaders vista) steps output ∧
      output.store 1=resultWord vista anchor leaders := by
  obtain ⟨steps,bounded,last,ran,halted,stored⟩ := routine_executes vista anchor leaders
  refine ⟨steps,last,bounded,⟨?_,halted⟩,?_⟩
  · have start : initial routine.program (AnchorMatrix.inputWord anchor leaders vista)=
        ⟨0,GaussianCalls.file (AnchorMatrix.inputWord anchor leaders vista) [] [] []⟩ := by
      apply congrArg (Config.mk _)
      funext r;fin_cases r <;> simp [GaussianCalls.file]
    rw [start]
    exact ran
  · rw [stored]
    simp [GaussianCalls.file]

end Counting.StackMachine.AnchorSolve
