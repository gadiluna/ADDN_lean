import Counting.StackGaussianLinearPrefix
import Counting.StackGaussianAugmentVector
import Counting.StackGaussianCheckComplete

namespace Counting.StackMachine.GaussianCalls
open Routine EncodingPrograms GaussianNormalMatrix GaussianEquationCheck
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000

abbrev saveSolution : Routine 54 := ofProgram (ListPrograms.copyProgram 53 1 54 55)
abbrev augmentVector : Routine 54 := relocate GaussianAugmentVector.routine (roles 3 (by decide))
abbrev assembleCheck : Routine 54 := sequence (ofProgram (unframeProgram 53 53 0 55))
  (sequence (clear 0) (sequence (move 53 53 0 55) (frameRoutine 53 1 0 55)))
abbrev check : Routine 54 := relocate (isolate GaussianCheck.complete) (roles 41 (by decide))
abbrev someCore : Routine 54 := sequence saveSolution
  (sequence forward (sequence augmentVector (sequence assembleCheck check)))
def checkCost (length : Nat) : Nat := 44*(1000000000000000*(length+1)^5+length+3)

theorem saveSolution_executes (solution original : List Bool) :
    Executes saveSolution (file [] solution original []) (5*solution.length+2)
      (file [] solution original solution) := by
  have ran := copy_executes 53 (1:Fin 56) 54 55 (by decide) (by decide) (by decide)
    (file [] solution original []) rfl
  have stored : Function.update (file [] solution original []) 54 (solution++[])=file [] solution original solution := by
    funext r;fin_cases r <;> simp [file]
  change Executes _ _ (5*solution.length+2) (Function.update (file [] solution original []) 54 (solution++[])) at ran
  rw [stored] at ran
  exact ran

theorem augmentVector_executes (values : List Rat) (original solution : List Bool) :
    ∃ time ≤ 100*((Encoding.rationalRow.encode values).length+1),
      Executes augmentVector (file (Encoding.rationalRow.encode values) [] original solution) time
        (file [] (Encoding.rationalRow.encode (vector values)) original solution) := by
  obtain ⟨time,bounded,ran⟩ := GaussianAugmentVector.executes values
  have input : GaussianAugmentVector.file (Encoding.rationalRow.encode values) [] []=
      inputStore 3 (Encoding.rationalRow.encode values) := by
    funext r;fin_cases r <;> simp [GaussianAugmentVector.file,inputStore]
  have output : GaussianAugmentVector.file [] (Encoding.rationalRow.encode (vector values)) []=
      outputStore 3 (Encoding.rationalRow.encode (vector values)) := by
    funext r;fin_cases r <;> simp [GaussianAugmentVector.file,outputStore]
  rw [input,output] at ran
  exact ⟨time,bounded,lift_executes _ _ _ _ original solution _ ran⟩

theorem assembleCheck_executes (width : Nat) (rows : List (List Rat)) (values : List Rat)
    (saved : List Bool) :
    Executes assembleCheck
      (file [] (Encoding.rationalRow.encode values) (GaussianNormal.inputWord width rows) saved)
      (6*width+6*(Encoding.rationalMatrix.encode rows).length+5*(Encoding.rationalRow.encode values).length+14)
      (file (GaussianCheck.inputCodec.encode (values,rows)) [] [] saved) := by
  let input := file [] (Encoding.rationalRow.encode values) (GaussianNormal.inputWord width rows) saved
  let parsed := file (List.replicate width true) (Encoding.rationalRow.encode values) (Encoding.rationalMatrix.encode rows) saved
  let erased := file [] (Encoding.rationalRow.encode values) (Encoding.rationalMatrix.encode rows) saved
  let moved := file (Encoding.rationalMatrix.encode rows) (Encoding.rationalRow.encode values) [] saved
  have a := unframe_canonical_executes 53 (53:Fin 56) 0 55 (by decide) (by decide) (by decide)
    input (List.replicate width true) (Encoding.rationalMatrix.encode rows) rfl rfl
  have parsedStore : Function.update (Function.update input 53 (Encoding.rationalMatrix.encode rows)) 0
      (List.replicate width true++[])=parsed := by
    funext r;fin_cases r <;> simp [input,parsed,file]
  change Executes _ input (5*(List.replicate width true).length+2)
    (Function.update (Function.update input 53 (Encoding.rationalMatrix.encode rows)) 0 (List.replicate width true++[])) at a
  rw [parsedStore,List.length_replicate] at a
  have b := clear_executes (registers:=54) 0 parsed
  have erasedStore : Function.update parsed 0 []=erased := by funext r;fin_cases r <;> simp [parsed,erased,file]
  rw [erasedStore] at b
  change Executes _ parsed ((List.replicate width true).length+1) erased at b
  rw [List.length_replicate] at b
  have c := move_executes 53 (53:Fin 56) 0 55 (by decide) (by decide) (by decide) erased rfl
  have movedStore : Function.update (Function.update erased 0 (erased 53++erased 0)) 53 []=moved := by
    funext r;fin_cases r <;> simp [erased,moved,file]
  rw [movedStore] at c
  change Executes _ erased (6*(Encoding.rationalMatrix.encode rows).length+4) moved at c
  have d := frame_executes 53 (1:Fin 56) 0 55 (by decide) (by decide) (by decide) moved rfl
  have finalStore : frameResult 53 1 0 55 moved=file (GaussianCheck.inputCodec.encode (values,rows)) [] [] saved := by
    funext r;fin_cases r <;> simp [frameResult,moved,file,GaussianCheck.inputCodec,Encoding.product,Encoding.framed]
  rw [finalStore] at d
  change Executes _ moved (5*(Encoding.rationalRow.encode values).length+4) _ at d
  convert a.sequence (b.sequence (c.sequence d)) using 1
  omega

theorem check_executes (rows : List (List Rat)) (values : List Rat)
    (same : ∀ row∈rows,row.length=values.length) (original solution : List Bool) :
    ∃ time ≤ checkCost (GaussianCheck.inputCodec.encode (values,rows)).length,
      Executes check (file (GaussianCheck.inputCodec.encode (values,rows)) [] original solution) time
        (file [] [accepts rows values] original solution) := by
  obtain ⟨time,bounded,ran⟩ := isolate_halts GaussianCheck.complete _ _ _ (GaussianCheck.complete_halts rows values same)
  exact ⟨time,bounded,lift_executes _ _ _ _ original solution _ ran⟩

def someCoreCost (width matrixLength solutionLength vectorLength checkerLength : Nat) : Nat :=
  11*solutionLength+100*(solutionLength+1)+6*width+6*matrixLength+5*vectorLength+checkCost checkerLength+24

theorem someCore_executes (width : Nat) (equations : List Executable.Equation) (solution : Fin width → Rat) :
    ∃ time ≤ someCoreCost width (Encoding.rationalMatrix.encode (equationMatrix width equations)).length
        (Encoding.rationalRow.encode (List.ofFn solution)).length
        (Encoding.rationalRow.encode (vector (List.ofFn solution))).length
        (GaussianCheck.inputCodec.encode (vector (List.ofFn solution),equationMatrix width equations)).length,
      Executes someCore
        (file [] (Encoding.rationalRow.encode (List.ofFn solution))
          (GaussianNormal.inputWord width (equationMatrix width equations)) []) time
        (file [] [accepts (equationMatrix width equations) (vector (List.ofFn solution))] []
          (Encoding.rationalRow.encode (List.ofFn solution))) := by
  let original := GaussianNormal.inputWord width (equationMatrix width equations)
  let word := Encoding.rationalRow.encode (List.ofFn solution)
  have a := saveSolution_executes word original
  have b := forward_executes word original word
  obtain ⟨augmentTime,augmentBound,c⟩ := augmentVector_executes (List.ofFn solution) original word
  have d := assembleCheck_executes width (equationMatrix width equations) (vector (List.ofFn solution)) word
  have same : ∀ row∈equationMatrix width equations,row.length=(vector (List.ofFn solution)).length := by
    intro row member
    obtain ⟨equation,_,rfl⟩ := List.mem_map.mp member
    simp
  obtain ⟨checkTime,checkBound,e⟩ := check_executes (equationMatrix width equations) (vector (List.ofFn solution)) same [] word
  refine ⟨_,?_,a.sequence (b.sequence (c.sequence (d.sequence e)))⟩
  dsimp only [someCoreCost,word]
  omega

end Counting.StackMachine.GaussianCalls
