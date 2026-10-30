import Counting.StackRationalEncoding

namespace Counting.StackMachine.RationalArithmetic
open Routine

set_option backward.isDefEq.respectTransparency false

/-- Reduced magnitudes are canonical bit lists, so emptiness is precisely
zero. Inspect and restore a nonempty magnitude, otherwise reset its sign. -/
def fixMagnitudeSign : Routine 14 where
  states := 5
  code state := match state.val with
    | 0 => .pop 3 1 3 4
    | 1 => .pop 5 2 2 2
    | 2 => .push 5 false 5
    | 3 => .push 3 false 5
    | 4 => .push 3 true 5
    | _ => .halt

theorem fixMagnitudeSign_executes (numerator denominator common magnitude divisor : List Bool) (sign : Bool) :
    Executes fixMagnitudeSign (file numerator denominator common magnitude divisor [sign])
      (if magnitude=[] then 3 else 2)
      (file numerator denominator common magnitude divisor [if magnitude=[] then false else sign]) := by
  cases magnitude with
  | nil =>
      refine ⟨⟨5,file numerator denominator common [] divisor [false]⟩,?_,rfl,rfl⟩
      cases sign <;> apply congrArg some <;> apply congrArg (Config.mk _)
      all_goals funext r; fin_cases r <;> rfl
  | cons bit rest =>
      refine ⟨⟨5,file numerator denominator common (bit::rest) divisor [sign]⟩,?_,rfl,rfl⟩
      cases bit <;> apply congrArg some <;> apply congrArg (Config.mk _)
      all_goals funext r; fin_cases r <;> rfl

abbrev formatDenominator : Routine 14 := Normalize.formatRoutine 13 4 1 7
abbrev formatNumerator : Routine 14 := Normalize.formatRoutine 13 3 1 7
abbrev formatNormalized : Routine 14 := sequence (clear 1)
  (sequence fixMagnitudeSign
    (sequence formatDenominator (sequence formatNumerator (Signed.readSign 5 1))))

theorem formatNormalized_executes (numerator denominator common : List Bool)
    (magnitude divisor : Nat) (sign : Bool) :
    ∃ time ≤ denominator.length+5*magnitude.bits.length+5*divisor.bits.length+25,
      Executes formatNormalized (file numerator denominator common magnitude.bits divisor.bits [sign]) time
        (file numerator
          (Encoding.integer.encode (Encoding.signedValue sign magnitude)++Encoding.natural.encode divisor)
          common [] [] []) := by
  have cleared := clear_executes (registers := 14) 1
    (file numerator denominator common magnitude.bits divisor.bits [sign])
  have clearStore : Function.update (file numerator denominator common magnitude.bits divisor.bits [sign]) 1 [] =
      file numerator [] common magnitude.bits divisor.bits [sign] := by
    funext r; fin_cases r <;> rfl
  change Executes (clear 1) _ (denominator.length+1) _ at cleared
  rw [clearStore] at cleared
  have fixed := fixMagnitudeSign_executes numerator [] common magnitude.bits divisor.bits sign
  have zero : magnitude.bits=[] ↔ magnitude=0 := by
    constructor
    · intro equal
      have := congrArg Encoding.value equal
      simpa [Encoding.value] using this
    · rintro rfl; rfl
  simp only [zero] at fixed
  change Executes fixMagnitudeSign _ (if magnitude=0 then 3 else 2)
    (file numerator [] common magnitude.bits divisor.bits [Signed.canonicalSign sign magnitude]) at fixed
  let actualSign := Signed.canonicalSign sign magnitude
  have den := Normalize.format_executes 13 4 1 7 (by decide) (by decide) (by decide)
    (file numerator [] common magnitude.bits divisor.bits [actualSign]) rfl
  change Executes formatDenominator _ (Normalize.formatCost divisor.bits)
    (Function.update (Function.update (file numerator [] common magnitude.bits divisor.bits [actualSign]) 4 []) 1
      (Encoding.natural.encode (Encoding.value divisor.bits)++[])) at den
  have denStore : Function.update
      (Function.update (file numerator [] common magnitude.bits divisor.bits [actualSign]) 4 []) 1
      (Encoding.natural.encode (Encoding.value divisor.bits)++[]) =
      file numerator (Encoding.natural.encode divisor) common magnitude.bits [] [actualSign] := by
    funext r; fin_cases r <;> simp [file,Encoding.value_bits]
  rw [denStore] at den
  have num := Normalize.format_executes 13 3 1 7 (by decide) (by decide) (by decide)
    (file numerator (Encoding.natural.encode divisor) common magnitude.bits [] [actualSign]) rfl
  change Executes formatNumerator _ (Normalize.formatCost magnitude.bits)
    (Function.update (Function.update
      (file numerator (Encoding.natural.encode divisor) common magnitude.bits [] [actualSign]) 3 []) 1
      (Encoding.natural.encode (Encoding.value magnitude.bits)++Encoding.natural.encode divisor)) at num
  have numStore : Function.update (Function.update
      (file numerator (Encoding.natural.encode divisor) common magnitude.bits [] [actualSign]) 3 []) 1
      (Encoding.natural.encode (Encoding.value magnitude.bits)++Encoding.natural.encode divisor) =
      file numerator (Encoding.natural.encode magnitude++Encoding.natural.encode divisor) common [] [] [actualSign] := by
    funext r; fin_cases r <;> simp [file,Encoding.value_bits]
  rw [numStore] at num
  have signed := Signed.readSign_executes (registers := 14) 5 1 (by decide)
    (file numerator (Encoding.natural.encode magnitude++Encoding.natural.encode divisor) common [] [] [actualSign])
  change Executes (Signed.readSign 5 1) _ 2
    (Function.update (Function.update
      (file numerator (Encoding.natural.encode magnitude++Encoding.natural.encode divisor) common [] [] [actualSign]) 5 []) 1
      (actualSign::(Encoding.natural.encode magnitude++Encoding.natural.encode divisor))) at signed
  have signStore : Function.update (Function.update
      (file numerator (Encoding.natural.encode magnitude++Encoding.natural.encode divisor) common [] [] [actualSign]) 5 []) 1
      (actualSign::(Encoding.natural.encode magnitude++Encoding.natural.encode divisor)) =
      file numerator (Encoding.integer.encode (Encoding.signedValue sign magnitude)++Encoding.natural.encode divisor)
        common [] [] [] := by
    rw [Signed.signed_integer_encode,List.cons_append]
    funext r; fin_cases r <;> rfl
  rw [signStore] at signed
  refine ⟨_,?_,cleared.sequence (fixed.sequence (den.sequence (num.sequence signed)))⟩
  have denBound := Normalize.formatCost_le divisor.bits
  have numBound := Normalize.formatCost_le magnitude.bits
  split_ifs <;> omega

end Counting.StackMachine.RationalArithmetic
