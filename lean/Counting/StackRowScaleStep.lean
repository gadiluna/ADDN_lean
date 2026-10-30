import Counting.StackRationalCall
import Counting.StackEncodingFrameStore
import Counting.EncodingRationalRows

namespace Counting.StackMachine.RowScale
open Routine EncodingPrograms

def file (factor input reversed counter item product header status framed : List Bool) : Fin 32 → List Bool :=
  ![factor,input,reversed,counter,item,product,header,[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],status,framed,[],[]]
def callRoles : Fin 24 ↪ Fin 32 := ⟨![0,4,5,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27],by decide⟩
abbrev readItem : Routine 30 := ofProgram (unframeProgram 29 1 4 7)
abbrev multiplyItem : Routine 30 := relocate RationalCall.multiplication callRoles
abbrev emitItem : Routine 30 := sequence (frameRoutine 29 5 29 7)
  (ofProgram (ListPrograms.reverseProgram 30 29 2))
abbrev body : Routine 30 := sequence readItem
  (sequence multiplyItem (sequence (clear 4) emitItem))

theorem readItem_executes (factor payload suffix reversed counter header status : List Bool) :
    Executes readItem (file factor (Encoding.frame payload++suffix) reversed counter [] [] header status [])
      (5*payload.length+2) (file factor suffix reversed counter payload [] header status []) := by
  let base := file factor (Encoding.frame payload++suffix) reversed counter [] [] header status []
  have start : unframeConfig 29 1 4 7 0 base (Encoding.frame payload++suffix) [] [] =
      (⟨0,base⟩ : Config (unframeProgram 29 1 4 7)) := by
    apply congrArg (Config.mk _)
    change (fun r : Fin 32 => _) = base
    funext r; fin_cases r <;> simp [base,file]
  have ran := unframe_frames 29 1 4 7 (by decide) (by decide) (by decide) base payload suffix []
  rw [start] at ran
  refine ⟨unframeConfig 29 1 4 7 7 base suffix (payload++[]) [],ran,(unframe_halted _ _ _ _ _ _ _ _).1,?_⟩
  change (fun r : Fin 32 => _) = _
  funext r; fin_cases r <;> simp [unframeConfig,base,file]

theorem multiplyItem_executes (factor input reversed counter item header status : List Bool) :
    ∃ time ≤ 90000000*(factor.length+item.length+1)^3,
      Executes multiplyItem (file factor input reversed counter item [] header status []) time
        (file factor input reversed counter item (RationalArithmetic.Product.productFunction (factor++item)) header status []) := by
  obtain ⟨time,bounded,ran⟩ := RationalCall.multiplication_executes factor item
  refine ⟨time,bounded,?_⟩
  apply relocate_executes_frame RationalCall.multiplication callRoles _ _ _ _ time _ _ _ ran
  · funext r; fin_cases r <;> simp [file,RationalCall.file,callRoles]
  · intro r; fin_cases r <;> simp [file,RationalCall.file,callRoles]
  · intro r outside
    fin_cases r
    · simp [file]
    · simp [file]
    · simp [file]
    · simp [file]
    · simp [file]
    · exact False.elim (outside 2 rfl)
    · simp [file]
    · simp [file]
    · simp [file]
    · simp [file]
    · simp [file]
    · simp [file]
    · simp [file]
    · simp [file]
    · simp [file]
    · simp [file]
    · simp [file]
    · simp [file]
    · simp [file]
    · simp [file]
    · simp [file]
    · simp [file]
    · simp [file]
    · simp [file]
    · simp [file]
    · simp [file]
    · simp [file]
    · simp [file]
    · simp [file]
    · simp [file]
    · simp [file]
    · simp [file]

theorem emitItem_executes (factor input reversed counter header status product : List Bool) :
    Executes emitItem (file factor input reversed counter [] product header status [])
      (9*product.length+8)
      (file factor input ((Encoding.frame product).reverse++reversed) counter [] [] header status []) := by
  have framed := frame_executes_updates 29 5 29 7 (by decide) (by decide) (by decide)
    (file factor input reversed counter [] product header status []) rfl
  have frameStore : Function.update (Function.update (file factor input reversed counter [] product header status []) 5 [])
      29 (Encoding.frame product++[]) = file factor input reversed counter [] [] header status (Encoding.frame product) := by
    funext r; fin_cases r <;> simp [file]
  change Executes (frameRoutine 29 5 29 7) _ (5*product.length+4)
    (Function.update (Function.update (file factor input reversed counter [] product header status []) 5 [])
      29 (Encoding.frame product++[])) at framed
  rw [frameStore] at framed
  have reversedRun := reverse_executes 30 29 2 (by decide)
    (file factor input reversed counter [] [] header status (Encoding.frame product))
  have reverseStore : Function.update (Function.update (file factor input reversed counter [] [] header status (Encoding.frame product)) 29 [])
      2 ((Encoding.frame product).reverse++reversed) =
      file factor input ((Encoding.frame product).reverse++reversed) counter [] [] header status [] := by
    funext r; fin_cases r <;> simp [file]
  change Executes _ _ (2*(Encoding.frame product).length+1)
    (Function.update (Function.update (file factor input reversed counter [] [] header status (Encoding.frame product)) 29 [])
      2 ((Encoding.frame product).reverse++reversed)) at reversedRun
  rw [reverseStore] at reversedRun
  convert framed.sequence reversedRun using 1
  rw [Encoding.frame_length]
  omega

theorem body_executes (factor item suffix reversed counter header status : List Bool) :
    ∃ time ≤ 150000000*(factor.length+item.length+1)^3,
      Executes body (file factor (Encoding.frame item++suffix) reversed counter [] [] header status []) time
        (file factor suffix
          ((Encoding.frame (RationalArithmetic.Product.productFunction (factor++item))).reverse++reversed)
          counter [] [] header status []) := by
  let product := RationalArithmetic.Product.productFunction (factor++item)
  have parsedRun := readItem_executes factor item suffix reversed counter header status
  obtain ⟨callTime,callBound,called⟩ := multiplyItem_executes factor suffix reversed counter item header status
  have cleared := clear_executes (registers := 30) 4 (file factor suffix reversed counter item product header status [])
  have clearedStore : Function.update (file factor suffix reversed counter item product header status []) 4 [] =
      file factor suffix reversed counter [] product header status [] := by
    funext r; fin_cases r <;> simp [file]
  change Executes (clear 4) _ (item.length+1)
    (Function.update (file factor suffix reversed counter item product header status []) 4 []) at cleared
  rw [clearedStore] at cleared
  have emitted := emitItem_executes factor suffix reversed counter header status product
  refine ⟨_,?_,parsedRun.sequence (called.sequence (cleared.sequence emitted))⟩
  have productBound := computed_length_le RationalArithmetic.Product.completeProduct
    RationalArithmetic.Product.productFunction (Complexity.polynomial 3000000 3)
    RationalArithmetic.Product.product_computes (factor++item)
  change product.length ≤ _ at productBound
  simp only [List.length_append,Complexity.polynomial] at productBound
  have linear : factor.length+item.length+1 ≤ (factor.length+item.length+1)^3 := by
    have square := Nat.one_le_pow' 2 (factor.length+item.length)
    have mul := Nat.mul_le_mul_left (factor.length+item.length+1) square
    nlinarith
  omega

end Counting.StackMachine.RowScale
