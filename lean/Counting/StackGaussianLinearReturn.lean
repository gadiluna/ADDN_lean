import Counting.StackGaussianLinearCheck
import Counting.StackEncodingBranch

namespace Counting.StackMachine.GaussianCalls
open Routine EncodingPrograms GaussianNormalMatrix GaussianEquationCheck
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000

abbrev acceptSolution : Routine 54 := sequence (move 53 54 1 55) (pushBit 1 true)
abbrev rejectSolution : Routine 54 := sequence (clear 53) (sequence (clear 54) (pushBit 1 false))
abbrev checkedReturn : Routine 54 := branchRoutine 1 acceptSolution rejectSolution
abbrev someCase : Routine 54 := sequence someCore checkedReturn
abbrev handleSolution : Routine 54 := branchRoutine 1 someCase rejectSolution

theorem acceptSolution_executes (word : List Bool) :
    Executes acceptSolution (file [] [] [] word) (6*word.length+6) (file [] (true::word) [] []) := by
  have a := move_executes 53 (54:Fin 56) 1 55 (by decide) (by decide) (by decide) (file [] [] [] word) rfl
  have moved : Function.update (Function.update (file [] [] [] word) 1 (word++[])) 54 []=
      file [] word [] [] := by funext r;fin_cases r <;> simp [file]
  change Executes _ _ (6*word.length+4)
    (Function.update (Function.update (file [] [] [] word) 1 (word++[])) 54 []) at a
  rw [moved] at a
  have b := pushBit_executes (1:Fin 56) true (file [] word [] [])
  have tagged : Function.update (file [] word [] []) 1 (true::word)=file [] (true::word) [] [] := by
    funext r;fin_cases r <;> simp [file]
  change Executes _ _ 1 (Function.update (file [] word [] []) 1 (true::word)) at b
  rw [tagged] at b
  convert a.sequence b using 1

theorem rejectSolution_executes (original solution : List Bool) :
    Executes rejectSolution (file [] [] original solution) (original.length+solution.length+5)
      (file [] [false] [] []) := by
  have a := clear_executes (registers:=54) 53 (file [] [] original solution)
  have cleared : Function.update (file [] [] original solution) 53 []=file [] [] [] solution := by
    funext r;fin_cases r <;> simp [file]
  change Executes _ _ (original.length+1) _ at a
  rw [cleared] at a
  have b := clear_executes (registers:=54) 54 (file [] [] [] solution)
  have erased : Function.update (file [] [] [] solution) 54 []=file [] [] [] [] := by
    funext r;fin_cases r <;> simp [file]
  change Executes _ _ (solution.length+1) _ at b
  rw [erased] at b
  have c := pushBit_executes (1:Fin 56) false (file [] [] [] [])
  have tagged : Function.update (file [] [] [] []) 1 [false]=file [] [false] [] [] := by
    funext r;fin_cases r <;> simp [file]
  change Executes _ _ 1 (Function.update (file [] [] [] []) 1 [false]) at c
  rw [tagged] at c
  convert a.sequence (b.sequence c) using 1
  omega

theorem checkedReturn_executes (values : List Rat) (accepted : Bool) :
    ∃ time ≤ 6*(Encoding.rationalRow.encode values).length+7,
      Executes checkedReturn (file [] [accepted] [] (Encoding.rationalRow.encode values)) time
        (file [] ((Encoding.optional Encoding.rationalRow).encode (if accepted then some values else none)) [] []) := by
  have popped : Function.update (file [] [accepted] [] (Encoding.rationalRow.encode values)) 1 []=
      file [] [] [] (Encoding.rationalRow.encode values) := by funext r;fin_cases r <;> simp [file]
  cases accepted
  · have ran := branch_executes_false (1:Fin 56) acceptSolution rejectSolution
      (file [] [false] [] (Encoding.rationalRow.encode values)) (file [] [false] [] []) []
      ((Encoding.rationalRow.encode values).length+5) rfl
      (by rw [popped];simpa using rejectSolution_executes [] (Encoding.rationalRow.encode values))
    exact ⟨_,by omega,ran⟩
  · have ran := branch_executes_true (1:Fin 56) acceptSolution rejectSolution
      (file [] [true] [] (Encoding.rationalRow.encode values))
      (file [] (true::Encoding.rationalRow.encode values) [] []) []
      (6*(Encoding.rationalRow.encode values).length+6) rfl
      (by rw [popped];exact acceptSolution_executes (Encoding.rationalRow.encode values))
    exact ⟨_,by omega,ran⟩

def successCost (width : Nat) (equations : List Executable.Equation) (solution : Fin width → Rat) : Nat :=
  someCoreCost width (Encoding.rationalMatrix.encode (equationMatrix width equations)).length
    (Encoding.rationalRow.encode (List.ofFn solution)).length
    (Encoding.rationalRow.encode (vector (List.ofFn solution))).length
    (GaussianCheck.inputCodec.encode (vector (List.ofFn solution),equationMatrix width equations)).length+
      6*(Encoding.rationalRow.encode (List.ofFn solution)).length+8

theorem someCase_executes (width : Nat) (equations : List Executable.Equation) (solution : Fin width → Rat) :
    ∃ time ≤ successCost width equations solution,
      Executes someCase
        (file [] (Encoding.rationalRow.encode (List.ofFn solution))
          (GaussianNormal.inputWord width (equationMatrix width equations)) []) time
        (file [] ((Encoding.optional Encoding.rationalRow).encode
          (if accepts (equationMatrix width equations) (vector (List.ofFn solution)) then
            some (List.ofFn solution) else none)) [] []) := by
  obtain ⟨coreTime,coreBound,a⟩ := someCore_executes width equations solution
  obtain ⟨returnTime,returnBound,b⟩ := checkedReturn_executes (List.ofFn solution)
    (accepts (equationMatrix width equations) (vector (List.ofFn solution)))
  exact ⟨_,by dsimp only [successCost];omega,a.sequence b⟩

def handleCost (width : Nat) (equations : List Executable.Equation) : Nat :=
  match StoredGaussian.solve? (Executable.normalSystem width equations) with
  | none => (GaussianNormal.inputWord width (equationMatrix width equations)).length+6
  | some solution => successCost width equations solution+1

theorem handleSolution_executes (width : Nat) (equations : List Executable.Equation) :
    ∃ time ≤ handleCost width equations,
      Executes handleSolution
        (file [] ((Encoding.optional Encoding.rationalRow).encode
          ((StoredGaussian.solve? (Executable.normalSystem width equations)).map List.ofFn))
          (GaussianNormal.inputWord width (equationMatrix width equations)) []) time
        (file [] ((Encoding.optional Encoding.rationalRow).encode (GaussianSolveLinear.result width equations)) [] []) := by
  cases found : StoredGaussian.solve? (Executable.normalSystem width equations) with
  | none =>
    let original := GaussianNormal.inputWord width (equationMatrix width equations)
    have popped : Function.update (file [] [false] original []) 1 []=file [] [] original [] := by
      funext r;fin_cases r <;> simp [file]
    have ran := branch_executes_false (1:Fin 56) someCase rejectSolution
      (file [] [false] original []) (file [] [false] [] []) [] (original.length+5) rfl
      (by rw [popped];simpa using rejectSolution_executes original [])
    have result : GaussianSolveLinear.result width equations=none := by
      simp only [GaussianSolveLinear.result,found,bind,Option.bind_none]
    refine ⟨original.length+6,by simp only [handleCost,found];exact le_refl _,?_⟩
    rw [result]
    convert ran using 1
    all_goals first | rfl | omega
  | some solution =>
    let original := GaussianNormal.inputWord width (equationMatrix width equations)
    let word := Encoding.rationalRow.encode (List.ofFn solution)
    obtain ⟨time,bounded,ran⟩ := someCase_executes width equations solution
    have popped : Function.update (file [] (true::word) original []) 1 word=file [] word original [] := by
      funext r;fin_cases r <;> simp [file]
    have executed := branch_executes_true (1:Fin 56) someCase rejectSolution
      (file [] (true::word) original []) _ word time rfl (by rw [popped];exact ran)
    refine ⟨1+time,by simp only [handleCost,found];omega,?_⟩
    have result : GaussianSolveLinear.result width equations=
        if accepts (equationMatrix width equations) (vector (List.ofFn solution)) then some (List.ofFn solution) else none := by
      simp only [GaussianSolveLinear.result,found,bind,Option.bind_some]
    rw [result]
    exact executed

end Counting.StackMachine.GaussianCalls
