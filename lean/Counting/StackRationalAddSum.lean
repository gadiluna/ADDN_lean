import Counting.StackRationalAddProducts
import Counting.StackRegisterFrames

namespace Counting.StackMachine.RationalArithmetic.Addition
open Routine

def sumRoles : Fin 12 ↪ Fin 22 := ⟨![12,9,6,7,13,14,15,16,4,5,10,17],by decide⟩
abbrev sumRoutine : Routine 20 := relocate Signed.additionRoutine sumRoles
abbrev clearInputs : Routine 20 := sequence (clear 0) (clear 1)
abbrev prepare : Routine 20 := sequence products (sequence sumRoutine clearInputs)

theorem sum_executes (a b c d left right denominator : List Bool) (sa sc : Bool) :
    ∃ time ≤ 12*(left.length+right.length)+19,
      Executes sumRoutine (file a b c d [sa] [sc] left right denominator [] [] []) time
        (file a b c d [] [] [] [] denominator (Signed.addBits sa sc left right).2
          [(Signed.addBits sa sc left right).1] []) := by
  obtain ⟨time,bounded,ran⟩ := Signed.addition_executes sa sc [] left right
  have restricted : (file a b c d [sa] [sc] left right denominator [] [] []) ∘ sumRoles =
      Signed.file [] left right [sa] [sc] [] [] [] [] := by
    funext r; fin_cases r <;> simp [file,Signed.file,sumRoles]
  refine ⟨time,bounded,?_⟩
  apply relocate_executes_frame Signed.additionRoutine sumRoles _ _ _ _ time restricted _ _ ran
  · intro source; fin_cases source <;> simp [file,Signed.file,sumRoles]
  · intro r outside
    fin_cases r
    · simp [file]
    · simp [file]
    · simp [file]
    · simp [file]
    · exact False.elim (outside 8 rfl)
    · exact False.elim (outside 9 rfl)
    · exact False.elim (outside 2 rfl)
    · exact False.elim (outside 3 rfl)
    · simp [file]
    · exact False.elim (outside 1 rfl)
    · exact False.elim (outside 10 rfl)
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

theorem clearInputs_executes (a b c d denominator numerator sign : List Bool) :
    Executes clearInputs (file a b c d [] [] [] [] denominator numerator sign []) (a.length+b.length+3)
      (file [] [] c d [] [] [] [] denominator numerator sign []) := by
  have first := clear_executes (registers := 20) 0 (file a b c d [] [] [] [] denominator numerator sign [])
  have firstStore : Function.update (file a b c d [] [] [] [] denominator numerator sign []) 0 [] =
      file [] b c d [] [] [] [] denominator numerator sign [] := by
    funext r; fin_cases r <;> simp [file]
  change Executes (clear 0) _ (a.length+1)
    (Function.update (file a b c d [] [] [] [] denominator numerator sign []) 0 []) at first
  rw [firstStore] at first
  have second := clear_executes (registers := 20) 1 (file [] b c d [] [] [] [] denominator numerator sign [])
  have secondStore : Function.update (file [] b c d [] [] [] [] denominator numerator sign []) 1 [] =
      file [] [] c d [] [] [] [] denominator numerator sign [] := by
    funext r; fin_cases r <;> simp [file]
  change Executes (clear 1) _ (b.length+1)
    (Function.update (file [] b c d [] [] [] [] denominator numerator sign []) 1 []) at second
  rw [secondStore] at second
  have composed := first.sequence second
  convert composed using 1
  omega

def rawSum (sa sc : Bool) (a b c d : Nat) : Bool × List Bool := Signed.addBits sa sc (a*d).bits (c*b).bits

theorem prepare_executes (a b c d : List Bool) (sa sc : Bool) :
    ∃ time ≤ 260000*(a.length+b.length+c.length+d.length+1)^3,
      Executes prepare (file a b c d [sa] [sc] [] [] [] [] [] []) time
        (file [] [] c d [] [] [] [] (Encoding.value b*Encoding.value d).bits
          (rawSum sa sc (Encoding.value a) (Encoding.value b) (Encoding.value c) (Encoding.value d)).2
          [(rawSum sa sc (Encoding.value a) (Encoding.value b) (Encoding.value c) (Encoding.value d)).1] []) := by
  let sum := rawSum sa sc (Encoding.value a) (Encoding.value b) (Encoding.value c) (Encoding.value d)
  obtain ⟨productTime,productBound,productsRan⟩ := products_executes a b c d [sa] [sc]
  obtain ⟨sumTime,sumBound,sumRan⟩ := sum_executes a b c d (Encoding.value a*Encoding.value d).bits
    (Encoding.value c*Encoding.value b).bits (Encoding.value b*Encoding.value d).bits sa sc
  have cleared := clearInputs_executes a b c d (Encoding.value b*Encoding.value d).bits sum.2 [sum.1]
  refine ⟨_,?_,productsRan.sequence (sumRan.sequence cleared)⟩
  have left := NaturalCall.product_bits_length a d
  have right := NaturalCall.product_bits_length c b
  have linear : a.length+b.length+c.length+d.length+1 ≤ (a.length+b.length+c.length+d.length+1)^3 := by
    have square := Nat.one_le_pow' 2 (a.length+b.length+c.length+d.length)
    have product := Nat.mul_le_mul_left (a.length+b.length+c.length+d.length+1) square
    nlinarith
  omega

end Counting.StackMachine.RationalArithmetic.Addition
