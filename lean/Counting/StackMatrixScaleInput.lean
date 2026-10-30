import Counting.StackMatrixScaleBounds
import Counting.StackUnframeCanonical

namespace Counting.StackMachine.MatrixScale
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false

/-- The index is an internal unary field bounded by the number of rows. -/
def inputWord (factor : Rat) (rows : List (List Rat)) (index : Nat) : List Bool :=
  Encoding.frame (Encoding.rational.encode factor)++Encoding.frame (List.replicate (index+1) true)++
    Encoding.rationalMatrix.encode rows

abbrev prepareInput : Routine 33 := sequence (move 32 0 32 3)
  (sequence (ofProgram (unframeProgram 32 32 0 3)) (ofProgram (unframeProgram 32 32 33 3)))
abbrev complete : Routine 33 := sequence prepareInput (sequence scaleRoutine (move 32 32 1 3))

theorem prepareInput_executes (factor : Rat) (rows : List (List Rat)) (index : Nat) :
    Executes prepareInput (file (inputWord factor rows index) [] [] [] [] [])
      (6*(inputWord factor rows index).length+5*(Encoding.rational.encode factor).length+5*(index+1)+10)
      (file (Encoding.rational.encode factor) (Encoding.rationalMatrix.encode rows)
        (List.replicate (index+1) true) [] [] []) := by
  let input := inputWord factor rows index
  let scalar := Encoding.rational.encode factor
  let indexCode := List.replicate (index+1) true
  let matrix := Encoding.rationalMatrix.encode rows
  have moved := move_executes 32 0 32 3 (by decide) (by decide) (by decide)
    (file input [] [] [] [] []) rfl
  have movedStore : Function.update (Function.update (file input [] [] [] [] []) 32 (input++[])) 0 [] =
      file [] input [] [] [] [] := by
    funext r;fin_cases r <;> simp [file,RowScale.file]
  change Executes _ _ (6*input.length+4)
    (Function.update (Function.update (file input [] [] [] [] []) 32 (input++[])) 0 []) at moved
  rw [movedStore] at moved
  have parsedFactor := unframe_canonical_executes 32 32 0 3 (by decide) (by decide) (by decide)
    (file [] input [] [] [] []) scalar (Encoding.frame indexCode++matrix)
    (by simp only [input,inputWord,scalar,indexCode,matrix,List.append_assoc];rfl) rfl
  have factorStore : Function.update (Function.update (file [] input [] [] [] []) 32
      (Encoding.frame indexCode++matrix)) 0 (scalar++[]) =
      file scalar (Encoding.frame indexCode++matrix) [] [] [] [] := by
    funext r;fin_cases r <;> simp [file,RowScale.file]
  change Executes _ _ (5*scalar.length+2)
    (Function.update (Function.update (file [] input [] [] [] []) 32
      (Encoding.frame indexCode++matrix)) 0 (scalar++[])) at parsedFactor
  rw [factorStore] at parsedFactor
  have parsedIndex := unframe_canonical_executes 32 32 33 3 (by decide) (by decide) (by decide)
    (file scalar (Encoding.frame indexCode++matrix) [] [] [] []) indexCode matrix rfl rfl
  have indexStore : Function.update (Function.update
      (file scalar (Encoding.frame indexCode++matrix) [] [] [] []) 32 matrix) 33 (indexCode++[]) =
      file scalar matrix indexCode [] [] [] := by
    funext r;fin_cases r <;> simp [file,RowScale.file]
  change Executes _ _ (5*indexCode.length+2)
    (Function.update (Function.update (file scalar (Encoding.frame indexCode++matrix) [] [] [] []) 32 matrix)
      33 (indexCode++[])) at parsedIndex
  rw [indexStore] at parsedIndex
  convert moved.sequence (parsedFactor.sequence parsedIndex) using 1
  simp only [indexCode,List.length_replicate,input,scalar]
  omega

theorem complete_halts (factor : Rat) (rows : List (List Rat)) (index : Fin rows.length) :
    ∃ steps output, steps≤150000000000*((inputWord factor rows index.val).length+1)^4 ∧
      HaltsAt complete.program (inputWord factor rows index.val) steps output ∧
      output.store 1=Encoding.rationalMatrix.encode (rows.set index.val (rows[index.val].map (factor*·))) := by
  let input := inputWord factor rows index.val
  let scalar := Encoding.rational.encode factor
  let matrix := Encoding.rationalMatrix.encode rows
  let result := Encoding.rationalMatrix.encode (rows.set index.val (rows[index.val].map (factor*·)))
  have prepared := prepareInput_executes factor rows index.val
  obtain ⟨scaleTime,scaleBound,scaled⟩ := scale_executes_polynomial factor rows index
  have moved := move_executes 32 32 1 3 (by decide) (by decide) (by decide)
    (file scalar result [] [] [] []) rfl
  have resultStore : Function.update (Function.update (file scalar result [] [] [] []) 1 (result++[])) 32 [] =
      file scalar [] [] result [] [] := by
    funext r;fin_cases r <;> simp [file,RowScale.file]
  change Executes _ _ (6*result.length+4)
    (Function.update (Function.update (file scalar result [] [] [] []) 1 (result++[])) 32 []) at moved
  rw [resultStore] at moved
  obtain ⟨last,ran,halted,stored⟩ := prepared.sequence (scaled.sequence moved)
  refine ⟨6*input.length+5*scalar.length+5*(index.val+1)+10+1+(scaleTime+1+(6*result.length+4)),
    last,?_,⟨?_,halted⟩,?_⟩
  · have inputLength : input.length=2*scalar.length+1+(2*(index.val+1)+1)+matrix.length := by
      simp [input,inputWord,scalar,matrix,Encoding.frame_length,Nat.add_assoc]
    have outputBound := result_length_le factor rows index
    have power := Nat.pow_le_pow_left (show 2*scalar.length+matrix.length+2 ≤ input.length+1 by omega) 4
    have linear := Nat.le_self_pow (by decide : 4≠0) (input.length+1)
    change scaleTime≤60000000000*(2*scalar.length+matrix.length+2)^4 at scaleBound
    change result.length≤6000000004*(2*scalar.length+matrix.length+2)^4 at outputBound
    change _≤150000000000*(input.length+1)^4
    omega
  · have start : initial complete.program input=⟨0,file input [] [] [] [] []⟩ := by
      apply congrArg (Config.mk _)
      funext r;fin_cases r <;> simp [file,RowScale.file]
    rw [start]
    exact ran
  · rw [stored]
    rfl

end Counting.StackMachine.MatrixScale
