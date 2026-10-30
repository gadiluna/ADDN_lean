import Counting.StackMatrixSwapBounds
import Counting.StackUnframeCanonical
import Counting.StackRoutineMove

namespace Counting.StackMachine.MatrixSwap
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false

/-- Unary row indices are bounded by the number of stored rows. Both fields
include the one-position offset past the matrix length header. -/
def inputWord (rows : List (List Rat)) (first second : Nat) : List Bool :=
  Encoding.frame (List.replicate (first+1) true)++
    Encoding.frame (List.replicate (second+1) true)++Encoding.rationalMatrix.encode rows

abbrev prepareInput : Routine 8 := sequence (ofProgram (unframeProgram 7 0 1 6))
  (ofProgram (unframeProgram 7 0 2 6))
abbrev complete : Routine 8 := sequence prepareInput (sequence swapRoutine (move 7 0 1 6))

theorem prepareInput_executes (rows : List (List Rat)) (first second : Nat) :
    Executes prepareInput (file (inputWord rows first second) [] [] [] [] [])
      (5*(first+1)+5*(second+1)+5)
      (file (Encoding.rationalMatrix.encode rows) (List.replicate (first+1) true)
        (List.replicate (second+1) true) [] [] []) := by
  let firstCode := List.replicate (first+1) true
  let secondCode := List.replicate (second+1) true
  let suffix := Encoding.frame secondCode++Encoding.rationalMatrix.encode rows
  have parseFirst := unframe_canonical_executes 7 0 1 6 (by decide) (by decide) (by decide)
    (file (inputWord rows first second) [] [] [] [] []) firstCode suffix
    (by simp only [file,inputWord,firstCode,secondCode,suffix,List.append_assoc];rfl) rfl
  have afterFirst : Function.update (Function.update (file (inputWord rows first second) [] [] [] [] []) 0 suffix)
      1 (firstCode++[]) = file suffix firstCode [] [] [] [] := by
    funext r; fin_cases r <;> simp [file]
  change Executes _ _ (5*firstCode.length+2)
    (Function.update (Function.update (file (inputWord rows first second) [] [] [] [] []) 0 suffix)
      1 (firstCode++[])) at parseFirst
  rw [afterFirst] at parseFirst
  have parseSecond := unframe_canonical_executes 7 0 2 6 (by decide) (by decide) (by decide)
    (file suffix firstCode [] [] [] []) secondCode (Encoding.rationalMatrix.encode rows) rfl rfl
  have afterSecond : Function.update (Function.update (file suffix firstCode [] [] [] []) 0 (Encoding.rationalMatrix.encode rows))
      2 (secondCode++[]) = file (Encoding.rationalMatrix.encode rows) firstCode secondCode [] [] [] := by
    funext r; fin_cases r <;> simp [file]
  change Executes _ _ (5*secondCode.length+2)
    (Function.update (Function.update (file suffix firstCode [] [] [] []) 0 (Encoding.rationalMatrix.encode rows))
      2 (secondCode++[])) at parseSecond
  rw [afterSecond] at parseSecond
  convert parseFirst.sequence parseSecond using 1
  simp [firstCode,secondCode]
  omega

theorem result_length_le (rows : List (List Rat)) (first second : Fin rows.length) :
    (Encoding.rationalMatrix.encode ((rows.set first.val rows[second.val]).set second.val rows[first.val])).length ≤
      5*(Encoding.rationalMatrix.encode rows).length+2 := by
  have left := Encoding.framedList_member_length_le Encoding.rationalRow rows rows[first.val]
    (List.getElem_mem first.isLt)
  have right := Encoding.framedList_member_length_le Encoding.rationalRow rows rows[second.val]
    (List.getElem_mem second.isLt)
  have once := Encoding.framedList_set_length_le Encoding.rationalRow rows first.val rows[second.val] first.isLt
  have twice := Encoding.framedList_set_length_le Encoding.rationalRow (rows.set first.val rows[second.val])
    second.val rows[first.val] (by simp [second.isLt])
  change _ ≤ (Encoding.rationalMatrix.encode rows).length at left right
  change (Encoding.rationalMatrix.encode (rows.set first.val rows[second.val])).length ≤
    (Encoding.rationalMatrix.encode rows).length+2*(Encoding.rationalRow.encode rows[second.val]).length+1 at once
  change (Encoding.rationalMatrix.encode ((rows.set first.val rows[second.val]).set second.val rows[first.val])).length ≤
    (Encoding.rationalMatrix.encode (rows.set first.val rows[second.val])).length+
    2*(Encoding.rationalRow.encode rows[first.val]).length+1 at twice
  omega

theorem complete_halts (rows : List (List Rat)) (first second : Fin rows.length) :
    ∃ steps output, steps ≤ 500*((inputWord rows first.val second.val).length+1) ∧
      HaltsAt complete.program (inputWord rows first.val second.val) steps output ∧
      output.store 1=Encoding.rationalMatrix.encode ((rows.set first.val rows[second.val]).set second.val rows[first.val]) := by
  let resultCode := Encoding.rationalMatrix.encode ((rows.set first.val rows[second.val]).set second.val rows[first.val])
  have prepared := prepareInput_executes rows first.val second.val
  obtain ⟨swapTime,swapBound,swapped⟩ := swap_executes_linear rows first second
  have moved := move_executes 7 0 1 6 (by decide) (by decide) (by decide) (file resultCode [] [] [] [] []) rfl
  have final : Function.update (Function.update (file resultCode [] [] [] [] []) 1 (resultCode++[])) 0 []=
      file [] resultCode [] [] [] [] := by
    funext r;fin_cases r <;> simp [file]
  change Executes _ _ (6*resultCode.length+4)
    (Function.update (Function.update (file resultCode [] [] [] [] []) 1 (resultCode++[])) 0 []) at moved
  rw [final] at moved
  obtain ⟨finish,ran,halted,stored⟩ := prepared.sequence (swapped.sequence moved)
  refine ⟨5*(first.val+1)+5*(second.val+1)+5+1+(swapTime+1+(6*resultCode.length+4)),
    finish,?_,⟨?_,halted⟩,?_⟩
  · have outputBound := result_length_le rows first second
    have inputLength : (inputWord rows first.val second.val).length=
        2*(first.val+1)+1+(2*(second.val+1)+1)+(Encoding.rationalMatrix.encode rows).length := by
      simp [inputWord,Encoding.frame_length,Nat.add_assoc]
    change resultCode.length ≤ _ at outputBound
    change 5*(first.val+1)+5*(second.val+1)+5+1+(swapTime+1+(6*resultCode.length+4)) ≤ _
    omega
  · have start : initial complete.program (inputWord rows first.val second.val)=
        ⟨0,file (inputWord rows first.val second.val) [] [] [] [] []⟩ := by
      apply congrArg (Config.mk _)
      funext r;fin_cases r <;> simp [file]
    rw [start]
    exact ran
  · rw [stored]
    rfl

end Counting.StackMachine.MatrixSwap
