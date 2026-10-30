import Counting.StackGaussianNormalEntry
import Counting.StackEncodingFrameStore

namespace Counting.StackMachine.GaussianNormal
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false

abbrev emitScalar : Routine 51 := sequence (frameRoutine 50 42 51 43)
  (ofProgram (ListPrograms.reverseProgram 51 51 47))

/-- Appending a scalar to the reversed row stream uses the real frame
encoder and a real reversal. The scalar source and temporary are emptied. -/
theorem emitScalar_executes (store : Fin 53 → List Bool)
    (temporary : store 51=[]) (scratch : store 43=[]) :
    Executes emitScalar store (9*(store 42).length+8)
      (Function.update (Function.update store 42 []) 47 ((Encoding.frame (store 42)).reverse++store 47)) := by
  have a := frame_executes_updates 50 (42 : Fin 53) 51 43 (by decide) (by decide) (by decide) store scratch
  let framed := Function.update (Function.update store 42 []) 51 (Encoding.frame (store 42))
  have aStore : Function.update (Function.update store 42 []) 51 (Encoding.frame (store 42)++store 51)=framed := by
    simp [framed,temporary]
  rw [aStore] at a
  have b := reverse_executes 51 (51 : Fin 53) 47 (by decide) framed
  have bStore : Function.update (Function.update framed 51 []) 47 ((framed 51).reverse++framed 47)=
      Function.update (Function.update store 42 []) 47 ((Encoding.frame (store 42)).reverse++store 47) := by
    funext r
    by_cases source : r=42
    · subst r;simp [framed]
    · by_cases target : r=47
      · subst r;simp [framed]
      · by_cases work : r=51
        · subst r;simp [framed,temporary]
        · simp [framed,source,target,work]
  rw [bStore] at b
  change Executes _ _ (2*(Encoding.frame (store 42)).length+1) _ at b
  convert a.sequence b using 1
  rw [Encoding.frame_length]
  omega

end Counting.StackMachine.GaussianNormal
