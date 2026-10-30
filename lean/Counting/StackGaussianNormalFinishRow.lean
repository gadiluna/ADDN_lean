import Counting.StackGaussianNormalEmit

namespace Counting.StackMachine.GaussianNormal
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false

abbrev finishRow : Routine 51 := sequence (ofProgram (ListPrograms.reverseProgram 51 47 51))
  (sequence (ofProgram (ListPrograms.copyProgram 50 49 51 52))
    (sequence (frameRoutine 50 51 42 43) (ofProgram (ListPrograms.reverseProgram 51 42 48))))

/-- Complete one row in its original column order, prefix the retained
binary length header, and append an outer framed row to the matrix stream. -/
theorem finishRow_executes (store : Fin 53 → List Bool) (temporary : store 51=[])
    (scalar : store 42=[]) (scratch : store 43=[]) (transfer : store 52=[]) :
    Executes finishRow store (11*(store 47).length+14*(store 49).length+13)
      (Function.update (Function.update store 47 []) 48
        ((Encoding.frame (store 49++(store 47).reverse)).reverse++store 48)) := by
  let reversed := Function.update (Function.update store 47 []) 51 (store 47).reverse
  let joined := Function.update (Function.update store 47 []) 51 (store 49++(store 47).reverse)
  let framed := Function.update (Function.update store 47 []) 42 (Encoding.frame (store 49++(store 47).reverse))
  have a := reverse_executes 51 (47 : Fin 53) 51 (by decide) store
  have aStore : Function.update (Function.update store 47 []) 51 ((store 47).reverse++store 51)=reversed := by
    simp [reversed,temporary]
  rw [aStore] at a
  change Executes (ofProgram (ListPrograms.reverseProgram 51 47 51)) store (2*(store 47).length+1) reversed at a
  have b := copy_executes 50 (49 : Fin 53) 51 52 (by decide) (by decide) (by decide) reversed
    (by simp [reversed,transfer])
  have bStore : Function.update reversed 51 (reversed 49++reversed 51)=joined := by
    simp [reversed,joined]
  rw [bStore] at b
  change Executes _ reversed (5*(store 49).length+2) joined at b
  have c := frame_executes_updates 50 (51 : Fin 53) 42 43 (by decide) (by decide) (by decide) joined
    (by simp [joined,scratch])
  have cStore : Function.update (Function.update joined 51 []) 42 (Encoding.frame (joined 51)++joined 42)=framed := by
    funext r;fin_cases r <;> simp [joined,framed,temporary,scalar]
  rw [cStore] at c
  change Executes _ joined (5*(store 49++(store 47).reverse).length+4) framed at c
  have d := reverse_executes 51 (42 : Fin 53) 48 (by decide) framed
  have dStore : Function.update (Function.update framed 42 []) 48 ((framed 42).reverse++framed 48)=
      Function.update (Function.update store 47 []) 48
        ((Encoding.frame (store 49++(store 47).reverse)).reverse++store 48) := by
    funext r;fin_cases r <;> simp [framed,scalar]
  rw [dStore] at d
  change Executes _ framed (2*(Encoding.frame (store 49++(store 47).reverse)).length+1) _ at d
  convert a.sequence (b.sequence (c.sequence d)) using 1
  · rfl
  · simp only [Encoding.frame_length,List.length_append,List.length_reverse]
    omega

end Counting.StackMachine.GaussianNormal
