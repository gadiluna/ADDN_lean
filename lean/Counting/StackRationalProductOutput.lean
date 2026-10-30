import Counting.StackRationalProductCorrectness
import Counting.StackRationalMachineOutput

namespace Counting.StackMachine.RationalArithmetic.Product
open Routine

abbrev formatRoutine : Routine 18 := relocate formatNormalized normalizeRoles
abbrev outputRoutine : Routine 18 := sequence formatRoutine (move 17 7 1 10)

theorem output_executes (c d numerator denominator common : List Bool) (magnitude divisor : Nat) (sign : Bool) :
    ∃ time ≤ denominator.length+17*magnitude.bits.length+17*divisor.bits.length+51,
      Executes outputRoutine (file magnitude.bits divisor.bits c d [] [] numerator denominator [sign] common) time
        (file [] (Encoding.integer.encode (Encoding.signedValue sign magnitude)++Encoding.natural.encode divisor)
          c d [] [] numerator [] [] common) := by
  obtain ⟨formatTime,formatBound,formatted⟩ := formatNormalized_executes numerator denominator common magnitude divisor sign
  have restricted : (file magnitude.bits divisor.bits c d [] [] numerator denominator [sign] common) ∘ normalizeRoles =
      RationalArithmetic.file numerator denominator common magnitude.bits divisor.bits [sign] := by
    funext r; fin_cases r <;> simp [file,RationalArithmetic.file,normalizeRoles]
  let encoded := Encoding.integer.encode (Encoding.signedValue sign magnitude)++Encoding.natural.encode divisor
  have localRan : Executes formatRoutine (file magnitude.bits divisor.bits c d [] [] numerator denominator [sign] common)
      formatTime (file [] [] c d [] [] numerator encoded [] common) := by
    apply relocate_executes_frame formatNormalized normalizeRoles _ _ _ _ formatTime restricted _ _ formatted
    · intro r; fin_cases r <;> simp [file,RationalArithmetic.file,normalizeRoles,encoded]
    · intro r outside
      fin_cases r
      · exact False.elim (outside 3 rfl)
      · exact False.elim (outside 4 rfl)
      · simp [file]
      · simp [file]
      · simp [file]
      · simp [file]
      · simp [file]
      · exact False.elim (outside 1 rfl)
      · exact False.elim (outside 5 rfl)
      all_goals simp [file]
  have moved := move_executes 17 7 1 10 (by decide) (by decide) (by decide)
    (file [] [] c d [] [] numerator encoded [] common) rfl
  have result : Function.update (Function.update (file [] [] c d [] [] numerator encoded [] common) 1 (encoded++[])) 7 [] =
      file [] encoded c d [] [] numerator [] [] common := by
    funext r; fin_cases r <;> simp [file]
  change Executes (move 17 7 1 10) _ (6*encoded.length+4)
    (Function.update (Function.update (file [] [] c d [] [] numerator encoded [] common) 1 (encoded++[])) 7 []) at moved
  rw [result] at moved
  refine ⟨_,?_,localRan.sequence moved⟩
  have encodedLen : encoded.length = 2*magnitude.bits.length+2*divisor.bits.length+3 := by
    simp [encoded,Encoding.integer_length,Encoding.natural_length,Signed.signed_natAbs,Encoding.bits_length]
    omega
  rw [encodedLen]
  omega

end Counting.StackMachine.RationalArithmetic.Product
