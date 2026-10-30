import Counting.StackRationalEncoding
import Counting.StackRegisterFrames

namespace Counting.StackMachine.RationalArithmetic.Reader
open Routine EncodingPrograms

def file (input numerator denominator sign flag : List Bool) : Fin 6 → List Bool :=
  ![input,numerator,denominator,sign,[],flag]
def roles : Fin 5 → Fin 6 := ![0,1,2,4,5]
abbrev reader : Routine 4 := sequence (Signed.readSign 0 3)
  (sequence (pairRoutine 1 roles) (clear 5))

theorem reader_executes (input : List Bool) :
    ∃ time ≤ 6*input.length+19,
      Executes reader (file input [] [] [] []) time
        (file (parsed input).suffix (parsed input).first (parsed input).second [parsedSign input] []) := by
  have signed := Signed.readSign_executes (registers := 4) 0 3 (by decide) (file input [] [] [] [])
  have signedStore : Function.update (Function.update (file input [] [] [] []) 0 input.tail) 3 [input.headD false] =
      file input.tail [] [] [parsedSign input] [] := by
    funext r; fin_cases r <;> simp [file,parsedSign]
  change Executes (Signed.readSign 0 3) _ 2
    (Function.update (Function.update (file input [] [] [] []) 0 input.tail) 3 [input.headD false]) at signed
  rw [signedStore] at signed
  obtain ⟨parseTime,parseBound,ran⟩ := pair_executes_spec 1 roles (by decide)
    (file input.tail [] [] [parsedSign input] []) rfl
  have parsedStore : pairExpected 1 roles (file input.tail [] [] [parsedSign input] []) =
      file (parsed input).suffix (parsed input).first (parsed input).second [parsedSign input] [(parsed input).accepted] := by
    funext r; fin_cases r <;> simp [pairExpected,roles,file,parsed]
  rw [parsedStore] at ran
  have cleared := clear_executes (registers := 4) 5
    (file (parsed input).suffix (parsed input).first (parsed input).second [parsedSign input] [(parsed input).accepted])
  have clearedStore : Function.update
      (file (parsed input).suffix (parsed input).first (parsed input).second [parsedSign input] [(parsed input).accepted]) 5 [] =
      file (parsed input).suffix (parsed input).first (parsed input).second [parsedSign input] [] := by
    funext r; fin_cases r <;> simp [file]
  change Executes (clear 5) _ 2 _ at cleared
  rw [clearedStore] at cleared
  refine ⟨_,?_,signed.sequence (ran.sequence cleared)⟩
  change parseTime ≤ 6*input.tail.length+13 at parseBound
  have tail : input.tail.length ≤ input.length := by simp
  omega

end Counting.StackMachine.RationalArithmetic.Reader
