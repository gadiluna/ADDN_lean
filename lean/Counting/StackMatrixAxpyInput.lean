import Counting.StackMatrixAxpyBounds
import Counting.StackUnframeCanonical

namespace Counting.StackMachine.MatrixAxpy
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false

def inputWord (factor : Rat) (rows : List (List Rat)) (target source : Nat) : List Bool :=
  Encoding.frame (Encoding.rational.encode factor)++Encoding.frame (List.replicate (target+1) true)++
    Encoding.frame (List.replicate (source+1) true)++Encoding.rationalMatrix.encode rows

abbrev prepareInput : Routine 40 := sequence (move 39 0 37 4)
  (sequence (ofProgram (unframeProgram 39 37 0 4))
    (sequence (ofProgram (unframeProgram 39 37 38 4)) (ofProgram (unframeProgram 39 37 39 4))))
abbrev complete : Routine 40 := sequence prepareInput (sequence axpyRoutine (move 39 37 1 4))
def completeCost : Nat := 100*(costConstant+RowAxpy.completeCost+1000)*3^16

theorem prepareInput_executes (factor : Rat) (rows : List (List Rat)) (target source : Nat) :
    Executes prepareInput (file (inputWord factor rows target source) [] [] [] [] [] [] [] [])
      (6*(inputWord factor rows target source).length+5*(Encoding.rational.encode factor).length+
        5*(target+1)+5*(source+1)+13)
      (file (Encoding.rational.encode factor) (Encoding.rationalMatrix.encode rows)
        (List.replicate (target+1) true) (List.replicate (source+1) true) [] [] [] [] []) := by
  let input := inputWord factor rows target source
  let scalar := Encoding.rational.encode factor
  let ti := List.replicate (target+1) true
  let si := List.replicate (source+1) true
  let matrix := Encoding.rationalMatrix.encode rows
  let rest := Encoding.frame ti++Encoding.frame si++matrix
  let finalRest := Encoding.frame si++matrix
  have moved := move_executes 39 0 37 4 (by decide) (by decide) (by decide)
    (file input [] [] [] [] [] [] [] []) rfl
  have movedStore : Function.update (Function.update (file input [] [] [] [] [] [] [] []) 37 (input++[])) 0 []=
      file [] input [] [] [] [] [] [] [] := by
    funext r;fin_cases r <;> simp [file,RowAxpy.file]
  change Executes _ _ (6*input.length+4)
    (Function.update (Function.update (file input [] [] [] [] [] [] [] []) 37 (input++[])) 0 []) at moved
  rw [movedStore] at moved
  have factorRun := unframe_canonical_executes 39 37 0 4 (by decide) (by decide) (by decide)
    (file [] input [] [] [] [] [] [] []) scalar rest
    (by simp only [input,inputWord,scalar,ti,si,matrix,rest,List.append_assoc];rfl) rfl
  have factorStore : Function.update (Function.update (file [] input [] [] [] [] [] [] []) 37 rest) 0 (scalar++[])=
      file scalar rest [] [] [] [] [] [] [] := by
    funext r;fin_cases r <;> simp [file,RowAxpy.file]
  change Executes _ _ (5*scalar.length+2)
    (Function.update (Function.update (file [] input [] [] [] [] [] [] []) 37 rest) 0 (scalar++[])) at factorRun
  rw [factorStore] at factorRun
  have targetRun := unframe_canonical_executes 39 37 38 4 (by decide) (by decide) (by decide)
    (file scalar rest [] [] [] [] [] [] []) ti finalRest (by simp only [rest,finalRest,List.append_assoc];rfl) rfl
  have targetStore : Function.update (Function.update (file scalar rest [] [] [] [] [] [] []) 37 finalRest) 38 (ti++[])=
      file scalar finalRest ti [] [] [] [] [] [] := by
    funext r;fin_cases r <;> simp [file,RowAxpy.file]
  change Executes _ _ (5*ti.length+2)
    (Function.update (Function.update (file scalar rest [] [] [] [] [] [] []) 37 finalRest) 38 (ti++[])) at targetRun
  rw [targetStore] at targetRun
  have sourceRun := unframe_canonical_executes 39 37 39 4 (by decide) (by decide) (by decide)
    (file scalar finalRest ti [] [] [] [] [] []) si matrix rfl rfl
  have sourceStore : Function.update (Function.update (file scalar finalRest ti [] [] [] [] [] []) 37 matrix) 39 (si++[])=
      file scalar matrix ti si [] [] [] [] [] := by
    funext r;fin_cases r <;> simp [file,RowAxpy.file]
  change Executes _ _ (5*si.length+2)
    (Function.update (Function.update (file scalar finalRest ti [] [] [] [] [] []) 37 matrix) 39 (si++[])) at sourceRun
  rw [sourceStore] at sourceRun
  convert moved.sequence (factorRun.sequence (targetRun.sequence sourceRun)) using 1
  simp only [ti,si,List.length_replicate,input,scalar]
  omega

theorem complete_halts (factor : Rat) (rows : List (List Rat)) (target source : Fin rows.length)
    (sameLength : rows[target.val].length=rows[source.val].length) :
    ∃ steps output,
      steps ≤ completeCost*((inputWord factor rows target.val source.val).length+1)^16 ∧
      HaltsAt complete.program (inputWord factor rows target.val source.val) steps output ∧
      output.store 1=Encoding.rationalMatrix.encode
        (rows.set target.val (List.zipWith (fun a b=>a+factor*b) rows[target.val] rows[source.val])) := by
  let input := inputWord factor rows target.val source.val
  let scalar := Encoding.rational.encode factor
  let matrix := Encoding.rationalMatrix.encode rows
  let result := Encoding.rationalMatrix.encode
    (rows.set target.val (List.zipWith (fun a b=>a+factor*b) rows[target.val] rows[source.val]))
  have prepared := prepareInput_executes factor rows target.val source.val
  obtain ⟨coreTime,coreBound,coreRun⟩ := axpy_executes_polynomial factor rows target source sameLength
  have moved := move_executes 39 37 1 4 (by decide) (by decide) (by decide)
    (file scalar result [] [] [] [] [] [] []) rfl
  have movedStore : Function.update (Function.update (file scalar result [] [] [] [] [] [] []) 1 (result++[])) 37 []=
      file scalar [] [] [] result [] [] [] [] := by
    funext r;fin_cases r <;> simp [file,RowAxpy.file]
  change Executes _ _ (6*result.length+4)
    (Function.update (Function.update (file scalar result [] [] [] [] [] [] []) 1 (result++[])) 37 []) at moved
  rw [movedStore] at moved
  obtain ⟨finish,ran,halted,stored⟩ := prepared.sequence (coreRun.sequence moved)
  refine ⟨6*input.length+5*scalar.length+5*(target.val+1)+5*(source.val+1)+13+1+(coreTime+1+(6*result.length+4)),
    finish,?_,⟨?_,halted⟩,?_⟩
  · have inputLength : input.length=2*scalar.length+1+(2*(target.val+1)+1)+(2*(source.val+1)+1)+matrix.length := by
      simp [input,inputWord,scalar,matrix,Encoding.frame_length,Nat.add_assoc]
    have outputBound := result_length_le factor rows target source sameLength
    have base : sizeBound factor rows ≤3*(input.length+1) := by change 2*scalar.length+3*matrix.length+3 ≤3*(input.length+1);omega
    have power := Nat.pow_le_pow_left base 16
    rw [Nat.mul_pow] at power
    have weightedCore := Nat.mul_le_mul_left costConstant power
    have weightedOutput := Nat.mul_le_mul_left (2*RowAxpy.completeCost+3) power
    have linear := Nat.le_self_pow (by decide : 16≠0) (input.length+1)
    change result.length ≤ _ at outputBound
    change _ ≤ completeCost*(input.length+1)^16
    unfold completeCost costConstant RowAxpy.completeCost RowAxpy.costConstant at *
    omega
  · have start : initial complete.program input=⟨0,file input [] [] [] [] [] [] [] []⟩ := by
      apply congrArg (Config.mk _)
      funext r;fin_cases r <;> simp [file,RowAxpy.file]
    rw [start]
    exact ran
  · rw [stored]
    rfl

end Counting.StackMachine.MatrixAxpy
