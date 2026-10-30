import Counting.StackGaussianNormalRows

namespace Counting.StackMachine.GaussianNormal
open Routine GaussianNormalMatrix
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000

abbrev finishMatrix : Routine 51 := sequence (ofProgram (ListPrograms.reverseProgram 51 48 51))
  (sequence (move 50 50 51 52) (move 50 51 1 52))
abbrev generate : Routine 51 := sequence rowsLoop finishMatrix

theorem finishMatrix_executes (store : Fin 53 → List Bool) (temporary : store 51=[])
    (outputEmpty : store 1=[]) (scratch : store 52=[]) :
    Executes finishMatrix store (8*(store 48).length+12*(store 50).length+11)
      (Function.update (Function.update (Function.update store 48 []) 50 []) 1 (store 50++(store 48).reverse)) := by
  let reversed := Function.update (Function.update store 48 []) 51 (store 48).reverse
  let joined := Function.update (Function.update (Function.update store 48 []) 50 []) 51 (store 50++(store 48).reverse)
  have a := reverse_executes 51 (48 : Fin 53) 51 (by decide) store
  have aStore : Function.update (Function.update store 48 []) 51 ((store 48).reverse++store 51)=reversed := by
    simp [reversed,temporary]
  rw [aStore] at a
  have b := move_executes 50 (50 : Fin 53) 51 52 (by decide) (by decide) (by decide) reversed
    (by simp [reversed,scratch])
  have bStore : Function.update (Function.update reversed 51 (reversed 50++reversed 51)) 50 []=joined := by
    funext r;fin_cases r <;> simp [reversed,joined]
  rw [bStore] at b
  change Executes _ reversed (6*(store 50).length+4) joined at b
  have c := move_executes 50 (51 : Fin 53) 1 52 (by decide) (by decide) (by decide) joined
    (by simp [joined,scratch])
  have cStore : Function.update (Function.update joined 1 (joined 51++joined 1)) 51 []=
      Function.update (Function.update (Function.update store 48 []) 50 []) 1 (store 50++(store 48).reverse) := by
    funext r;fin_cases r <;> simp [joined,temporary,outputEmpty]
  rw [cStore] at c
  change Executes _ joined (6*(store 50++(store 48).reverse).length+4) _ at c
  convert a.sequence (b.sequence c) using 1
  · rfl
  · simp only [List.length_append,List.length_reverse]
    omega

def outputStore (width : Nat) (equations : List Executable.Equation) : Fin 53 → List Bool :=
  Function.update (Function.update (state width equations width 0 [] [] [] [] []) 50 []) 1
    (Encoding.rationalMatrix.encode (StoredGaussian.augmentedMatrix (Executable.normalSystem width equations)))

/-- The result is the canonical encoding of the exact augmented normal
system, rather than an abstract array written without machine cost. -/
theorem generate_executes (width : Nat) (equations : List Executable.Equation) :
    ∃ time ≤ width*(rowBudget (Encoding.rationalMatrix.encode (equationMatrix width equations)).length width+2)+
        8*(Encoding.sequence (Encoding.framed Encoding.rationalRow)
          (StoredGaussian.augmentedMatrix (Executable.normalSystem width equations))).length+
        12*(Encoding.natural.encode width).length+13,
      Executes generate (state width equations 0 0 [] (List.replicate width true) [] [] []) time
        (outputStore width equations) := by
  let result := StoredGaussian.augmentedMatrix (Executable.normalSystem width equations)
  let stream := Encoding.sequence (Encoding.framed Encoding.rationalRow) result
  obtain ⟨loopTime,loopBound,a⟩ := rowsLoop_executes width equations 0 width (by omega) []
  rw [matrixRows_full] at a
  simp only [Nat.zero_add,List.append_nil] at a
  let afterLoop := state width equations width 0 [] [] [] stream.reverse []
  have b := finishMatrix_executes afterLoop rfl rfl rfl
  have encoded : Encoding.natural.encode width++stream=Encoding.rationalMatrix.encode result := by
    have length : result.length=width := by simp [result]
    change _=Encoding.natural.encode result.length++stream
    rw [length]
  have final : Function.update (Function.update (Function.update afterLoop 48 []) 50 []) 1
      (afterLoop 50++(afterLoop 48).reverse)=outputStore width equations := by
    funext r;fin_cases r <;> simp [afterLoop,state,outerBank,ready,bank,outputStore,encoded,result]
  rw [final] at b
  change Executes _ afterLoop (8*stream.reverse.length+12*(Encoding.natural.encode width).length+11) _ at b
  rw [List.length_reverse] at b
  refine ⟨_,?_,a.sequence b⟩
  dsimp only [stream,result]
  omega

end Counting.StackMachine.GaussianNormal
