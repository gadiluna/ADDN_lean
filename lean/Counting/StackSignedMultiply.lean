import Counting.StackSignedOutput
import Counting.StackRoutineRelocate

namespace Counting.StackMachine.Signed.Multiply
open Routine

def addresses : Fin 7 ↪ Fin 12 := ⟨fun index => ⟨index.val,by omega⟩,
  by intro a b equal; exact Fin.ext (congrArg (fun index : Fin 12 => index.val) equal)⟩

abbrev magnitude : Routine 10 := relocate Binary.multiplyRoutine addresses

abbrev signCase (first : Bool) : Routine 10 := EncodingPrograms.branchRoutine 9
  (pushBit 10 (!first)) (pushBit 10 first)
abbrev productSign : Routine 10 := EncodingPrograms.branchRoutine 8 (signCase true) (signCase false)
abbrev productCore : Routine 10 := sequence magnitude (sequence (clear 2) productSign)
abbrev productParsed : Routine 10 := sequence parser productCore
abbrev productRoutine : Routine 10 := sequence productParsed formatOutput

theorem magnitude_executes (input first second : List Bool) (firstSign secondSign : Bool) :
    ∃ time ≤ 12*second.length*
        (second.length*(first.length+second.length+1)+first.length+second.length+2)+1,
      Executes magnitude (file input first second [firstSign] [secondSign] [] [] [] []) time
        (file input (List.replicate second.length false++first) [] [firstSign] [secondSign]
          (Binary.multiplyBits first second) [] [] []) := by
  obtain ⟨time,bounded,ran⟩ := Binary.multiply_payloads first second input
  have restricted : (file input first second [firstSign] [secondSign] [] [] [] []) ∘ addresses =
      Binary.file input [] first second [] [] [] := by
    funext index; fin_cases index <;> rfl
  have relocated := relocate_executes Binary.multiplyRoutine addresses
    (file input first second [firstSign] [secondSign] [] [] [] []) time
    (Binary.file input (Binary.multiplyBits first second) (List.replicate second.length false++first) [] [] [] [])
    (by rw [restricted]; exact ran)
  have result : relocatedStore addresses (file input first second [firstSign] [secondSign] [] [] [] [])
      (Binary.file input (Binary.multiplyBits first second) (List.replicate second.length false++first) [] [] [] []) =
      file input (List.replicate second.length false++first) [] [firstSign] [secondSign]
        (Binary.multiplyBits first second) [] [] [] := by
    funext index
    fin_cases index
    all_goals first
    | exact relocatedStore_at addresses _ _ ⟨0,by decide⟩
    | exact relocatedStore_at addresses _ _ ⟨1,by decide⟩
    | exact relocatedStore_at addresses _ _ ⟨2,by decide⟩
    | exact relocatedStore_at addresses _ _ ⟨3,by decide⟩
    | exact relocatedStore_at addresses _ _ ⟨4,by decide⟩
    | exact relocatedStore_at addresses _ _ ⟨5,by decide⟩
    | exact relocatedStore_at addresses _ _ ⟨6,by decide⟩
    | apply relocatedStore_outside; intro source; apply Fin.ne_of_val_ne; dsimp [addresses]; omega
  rw [result] at relocated
  exact ⟨time,bounded,relocated⟩

theorem productSign_executes (input payload : List Bool) (firstSign secondSign : Bool) :
    Executes productSign (file input [] [] [firstSign] [secondSign] payload [] [] []) 3
      (file input [] [] [] [] payload [xor firstSign secondSign] [] []) := by
  have pushed (sign : Bool) := sign_executes sign input payload
  have resetSecond : Function.update (file input [] [] [] [secondSign] payload [] [] []) 9 [] =
      file input [] [] [] [] payload [] [] [] := by
    funext r; fin_cases r <;> rfl
  have resetFirst : Function.update (file input [] [] [firstSign] [secondSign] payload [] [] []) 8 [] =
      file input [] [] [] [secondSign] payload [] [] [] := by
    funext r; fin_cases r <;> rfl
  have second := branch_bit 9 (pushBit 10 (!firstSign)) (pushBit 10 firstSign)
    (file input [] [] [] [secondSign] payload [] [] [])
    (file input [] [] [] [] payload [xor firstSign secondSign] [] []) secondSign 1 rfl
    (by rw [resetSecond]; cases firstSign <;> cases secondSign <;> exact pushed _)
  have first := branch_bit 8 (signCase true) (signCase false)
    (file input [] [] [firstSign] [secondSign] payload [] [] [])
    (file input [] [] [] [] payload [xor firstSign secondSign] [] []) firstSign 2 rfl
    (by rw [resetFirst]; cases firstSign <;> exact second)
  exact first

theorem productCore_executes (input first second : List Bool) (firstSign secondSign : Bool) :
    ∃ time ≤ 30*(first.length+second.length+1)^3,
      Executes productCore (file input first second [firstSign] [secondSign] [] [] [] []) time
        (file input [] [] [] [] (Binary.multiplyBits first second) [xor firstSign secondSign] [] []) := by
  obtain ⟨time,bounded,ran⟩ := magnitude_executes input first second firstSign secondSign
  let shifted := List.replicate second.length false++first
  have cleared := clear_executes (registers := 10) 2
    (file input shifted [] [firstSign] [secondSign] (Binary.multiplyBits first second) [] [] [])
  change Executes (clear 2)
    (file input shifted [] [firstSign] [secondSign] (Binary.multiplyBits first second) [] [] []) (shifted.length+1)
    (Function.update (file input shifted [] [firstSign] [secondSign] (Binary.multiplyBits first second) [] [] []) 2 []) at cleared
  have clearResult : Function.update
      (file input shifted [] [firstSign] [secondSign] (Binary.multiplyBits first second) [] [] []) 2 [] =
      file input [] [] [firstSign] [secondSign] (Binary.multiplyBits first second) [] [] [] := by
    funext r; fin_cases r <;> rfl
  rw [clearResult] at cleared
  have sign := productSign_executes input (Binary.multiplyBits first second) firstSign secondSign
  refine ⟨_,?_,ran.sequence (cleared.sequence sign)⟩
  have multBound : second.length*(first.length+second.length+1) ≤
      (first.length+second.length)*(first.length+second.length+1) := by nlinarith
  have square := Nat.one_le_pow' 2 (first.length+second.length)
  have potential : second.length*(first.length+second.length+1)+first.length+second.length+2 ≤
      2*(first.length+second.length+1)^2 := by nlinarith
  have product := Nat.mul_le_mul (show second.length ≤ first.length+second.length+1 by omega) potential
  simp only [shifted,List.length_append,List.length_replicate]
  nlinarith

def signedProductFunction (input : List Bool) : List Bool :=
  Encoding.integer.encode (value (parsedFirst input).1 (parsedFirst input).2 *
    value (parsedSecond input).1 (parsedSecond input).2)

theorem product_value (firstSign secondSign : Bool) (first second : List Bool) :
    value (xor firstSign secondSign) (Binary.multiplyBits first second) =
      value firstSign first * value secondSign second := by
  unfold value
  rw [Binary.multiplyBits_value]
  cases firstSign <;> cases secondSign <;> simp [Encoding.signedValue]

end Counting.StackMachine.Signed.Multiply
