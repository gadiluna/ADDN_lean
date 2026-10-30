import Counting.StackRationalAddCall
import Counting.StackEncodingFrameStore
import Counting.EncodingRationalRows

namespace Counting.StackMachine.RowAdd
open Routine EncodingPrograms

def file (left right reversed counter first second sum framed header status auxiliary : List Bool) : Fin 36 → List Bool :=
  ![left,right,reversed,counter,first,second,header,[],sum,framed,[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],status,auxiliary,[],[]]
def callRoles : Fin 26 ↪ Fin 36 := ⟨![4,5,8,7,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31],by decide⟩
abbrev readLeft : Routine 34 := ofProgram (unframeProgram 33 0 4 7)
abbrev readRight : Routine 34 := ofProgram (unframeProgram 33 1 5 7)
abbrev addItems : Routine 34 := relocate RationalAddCall.addition callRoles
abbrev emitItem : Routine 34 := sequence (frameRoutine 33 8 9 7)
  (ofProgram (ListPrograms.reverseProgram 34 9 2))
abbrev body : Routine 34 := sequence readLeft (sequence readRight
  (sequence addItems (sequence (clear 4) (sequence (clear 5) emitItem))))

theorem readLeft_executes (payload suffix right reversed counter header status : List Bool) :
    Executes readLeft (file (Encoding.frame payload++suffix) right reversed counter [] [] [] [] header status [])
      (5*payload.length+2) (file suffix right reversed counter payload [] [] [] header status []) := by
  let base := file (Encoding.frame payload++suffix) right reversed counter [] [] [] [] header status []
  have start : unframeConfig 33 0 4 7 0 base (Encoding.frame payload++suffix) [] [] =
      (⟨0,base⟩ : Config (unframeProgram 33 0 4 7)) := by
    apply congrArg (Config.mk _)
    change (fun r : Fin 36 => _) = base
    funext r; fin_cases r <;> simp [base,file]
  have ran := unframe_frames 33 0 4 7 (by decide) (by decide) (by decide) base payload suffix []
  rw [start] at ran
  refine ⟨unframeConfig 33 0 4 7 7 base suffix (payload++[]) [],ran,(unframe_halted _ _ _ _ _ _ _ _).1,?_⟩
  change (fun r : Fin 36 => _) = _
  funext r; fin_cases r <;> simp [unframeConfig,base,file]

theorem readRight_executes (left payload suffix reversed counter first header status : List Bool) :
    Executes readRight (file left (Encoding.frame payload++suffix) reversed counter first [] [] [] header status [])
      (5*payload.length+2) (file left suffix reversed counter first payload [] [] header status []) := by
  let base := file left (Encoding.frame payload++suffix) reversed counter first [] [] [] header status []
  have start : unframeConfig 33 1 5 7 0 base (Encoding.frame payload++suffix) [] [] =
      (⟨0,base⟩ : Config (unframeProgram 33 1 5 7)) := by
    apply congrArg (Config.mk _)
    change (fun r : Fin 36 => _) = base
    funext r; fin_cases r <;> simp [base,file]
  have ran := unframe_frames 33 1 5 7 (by decide) (by decide) (by decide) base payload suffix []
  rw [start] at ran
  refine ⟨unframeConfig 33 1 5 7 7 base suffix (payload++[]) [],ran,(unframe_halted _ _ _ _ _ _ _ _).1,?_⟩
  change (fun r : Fin 36 => _) = _
  funext r; fin_cases r <;> simp [unframeConfig,base,file]

theorem addItems_executes (left right reversed counter first second header status : List Bool) :
    ∃ time ≤ 500000000*(first.length+second.length+1)^3,
      Executes addItems (file left right reversed counter first second [] [] header status []) time
        (file left right reversed counter first second (RationalArithmetic.Addition.additionFunction (first++second)) [] header status []) := by
  obtain ⟨time,bounded,ran⟩ := RationalAddCall.addition_executes first second
  refine ⟨time,bounded,?_⟩
  apply relocate_executes_frame RationalAddCall.addition callRoles _ _ _ _ time _ _ _ ran
  · funext r; fin_cases r <;> simp [file,RationalAddCall.file,callRoles]
  · intro r; fin_cases r <;> simp [file,RationalAddCall.file,callRoles]
  · intro r outside
    fin_cases r
    · simp [file]
    · simp [file]
    · simp [file]
    · simp [file]
    · simp [file]
    · simp [file]
    · simp [file]
    · simp [file]
    · exact False.elim (outside 2 rfl)
    all_goals simp [file]

theorem emitItem_executes (left right reversed counter header status sum : List Bool) :
    Executes emitItem (file left right reversed counter [] [] sum [] header status [])
      (9*sum.length+8)
      (file left right ((Encoding.frame sum).reverse++reversed) counter [] [] [] [] header status []) := by
  have framed := frame_executes_updates 33 8 9 7 (by decide) (by decide) (by decide)
    (file left right reversed counter [] [] sum [] header status []) rfl
  have frameStore : Function.update (Function.update (file left right reversed counter [] [] sum [] header status []) 8 [])
      9 (Encoding.frame sum++[]) = file left right reversed counter [] [] [] (Encoding.frame sum) header status [] := by
    funext r; fin_cases r <;> simp [file]
  change Executes (frameRoutine 33 8 9 7) _ (5*sum.length+4)
    (Function.update (Function.update (file left right reversed counter [] [] sum [] header status []) 8 [])
      9 (Encoding.frame sum++[])) at framed
  rw [frameStore] at framed
  have reversedRun := reverse_executes 34 9 2 (by decide)
    (file left right reversed counter [] [] [] (Encoding.frame sum) header status [])
  have reverseStore : Function.update (Function.update (file left right reversed counter [] [] [] (Encoding.frame sum) header status []) 9 [])
      2 ((Encoding.frame sum).reverse++reversed) =
      file left right ((Encoding.frame sum).reverse++reversed) counter [] [] [] [] header status [] := by
    funext r; fin_cases r <;> simp [file]
  change Executes _ _ (2*(Encoding.frame sum).length+1)
    (Function.update (Function.update (file left right reversed counter [] [] [] (Encoding.frame sum) header status []) 9 [])
      2 ((Encoding.frame sum).reverse++reversed)) at reversedRun
  rw [reverseStore] at reversedRun
  convert framed.sequence reversedRun using 1
  rw [Encoding.frame_length]
  omega

theorem body_executes (first second leftSuffix rightSuffix reversed counter header status : List Bool) :
    ∃ time ≤ 700000000*(first.length+second.length+1)^3,
      Executes body (file (Encoding.frame first++leftSuffix) (Encoding.frame second++rightSuffix) reversed counter [] [] [] [] header status []) time
        (file leftSuffix rightSuffix
          ((Encoding.frame (RationalArithmetic.Addition.additionFunction (first++second))).reverse++reversed)
          counter [] [] [] [] header status []) := by
  let sum := RationalArithmetic.Addition.additionFunction (first++second)
  have parsedLeft := readLeft_executes first leftSuffix (Encoding.frame second++rightSuffix) reversed counter header status
  have parsedRight := readRight_executes leftSuffix second rightSuffix reversed counter first header status
  obtain ⟨callTime,callBound,called⟩ := addItems_executes leftSuffix rightSuffix reversed counter first second header status
  have clearedLeft := clear_executes (registers := 34) 4 (file leftSuffix rightSuffix reversed counter first second sum [] header status [])
  have clearedLeftStore : Function.update (file leftSuffix rightSuffix reversed counter first second sum [] header status []) 4 [] =
      file leftSuffix rightSuffix reversed counter [] second sum [] header status [] := by
    funext r; fin_cases r <;> simp [file]
  change Executes (clear 4) _ (first.length+1)
    (Function.update (file leftSuffix rightSuffix reversed counter first second sum [] header status []) 4 []) at clearedLeft
  rw [clearedLeftStore] at clearedLeft
  have clearedRight := clear_executes (registers := 34) 5 (file leftSuffix rightSuffix reversed counter [] second sum [] header status [])
  have clearedRightStore : Function.update (file leftSuffix rightSuffix reversed counter [] second sum [] header status []) 5 [] =
      file leftSuffix rightSuffix reversed counter [] [] sum [] header status [] := by
    funext r; fin_cases r <;> simp [file]
  change Executes (clear 5) _ (second.length+1)
    (Function.update (file leftSuffix rightSuffix reversed counter [] second sum [] header status []) 5 []) at clearedRight
  rw [clearedRightStore] at clearedRight
  have emitted := emitItem_executes leftSuffix rightSuffix reversed counter header status sum
  refine ⟨_,?_,parsedLeft.sequence (parsedRight.sequence (called.sequence (clearedLeft.sequence (clearedRight.sequence emitted))))⟩
  have sumBound := computed_length_le RationalArithmetic.Addition.completeAddition
    RationalArithmetic.Addition.additionFunction (Complexity.polynomial 14000000 3)
    RationalArithmetic.Addition.addition_computes (first++second)
  change sum.length ≤ _ at sumBound
  simp only [List.length_append,Complexity.polynomial] at sumBound
  have linear : first.length+second.length+1 ≤ (first.length+second.length+1)^3 := by
    have square := Nat.one_le_pow' 2 (first.length+second.length)
    have product := Nat.mul_le_mul_left (first.length+second.length+1) square
    nlinarith
  omega

end Counting.StackMachine.RowAdd
