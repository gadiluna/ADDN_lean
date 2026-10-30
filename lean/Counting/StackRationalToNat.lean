import Counting.StackRationalPredicateSpec
import Counting.StackNormalize

namespace Counting.StackMachine.RationalArithmetic
open Routine

abbrev nonnegativeNumerator : Routine 14 := EncodingPrograms.branchRoutine 5 (clear 0) (skip 14)
abbrev numeratorToNatRoutine : Routine 14 := sequence rationalParser
  (sequence nonnegativeNumerator (sequence (clear 1) (Normalize.formatRoutine 13 0 1 7)))

def numeratorNatural (input : List Bool) : Nat :=
  if parsedSign input then 0 else Encoding.value (parsed input).first

theorem nonnegativeNumerator_executes (num den : List Bool) (sign : Bool) :
    Executes nonnegativeNumerator (file num den [] [] [] [sign]) (1+(if sign then num.length+1 else 0))
      (file (if sign then [] else num) den [] [] [] []) := by
  have reset : Function.update (file num den [] [] [] [sign]) 5 [] = file num den [] [] [] [] := by
    funext r; fin_cases r <;> simp [file]
  apply Signed.branch_bit 5 (clear 0) (skip 14) _ _ sign _ rfl
  rw [reset]
  cases sign
  · exact skip_executes (registers := 14) _
  · have cleared := clear_executes (registers := 14) 0 (file num den [] [] [] [])
    have result : Function.update (file num den [] [] [] []) 0 [] = file [] den [] [] [] [] := by
      funext r; fin_cases r <;> simp [file]
    change Executes (clear 0) _ (num.length+1) (Function.update (file num den [] [] [] []) 0 []) at cleared
    rw [result] at cleared
    exact cleared

theorem numeratorToNat_computes : ComputesIn numeratorToNatRoutine.program
    (fun input => Encoding.natural.encode (numeratorNatural input)) (Complexity.polynomial 50 1) := by
  intro input
  let num := (parsed input).first
  let den := (parsed input).second
  let sign := parsedSign input
  let magnitude := if sign then [] else num
  obtain ⟨parseTime,parseBound,parsedRun⟩ := rationalParser_executes input
  have selected := nonnegativeNumerator_executes num den sign
  have cleared := clear_executes (registers := 14) 1 (file magnitude den [] [] [] [])
  have clearStore : Function.update (file magnitude den [] [] [] []) 1 [] = file magnitude [] [] [] [] [] := by
    funext r; fin_cases r <;> simp [file]
  change Executes (clear 1) _ (den.length+1) (Function.update (file magnitude den [] [] [] []) 1 []) at cleared
  rw [clearStore] at cleared
  have formatted := Normalize.format_executes 13 0 1 7 (by decide) (by decide) (by decide)
    (file magnitude [] [] [] [] []) rfl
  have outputStore : Function.update (Function.update (file magnitude [] [] [] [] []) 0 []) 1
      (Encoding.natural.encode (Encoding.value magnitude)++[]) =
      file [] (Encoding.natural.encode (Encoding.value magnitude)) [] [] [] [] := by
    funext r; fin_cases r <;> simp [file]
  change Executes (Normalize.formatRoutine 13 0 1 7) _ (Normalize.formatCost magnitude)
    (Function.update (Function.update (file magnitude [] [] [] [] []) 0 []) 1
      (Encoding.natural.encode (Encoding.value magnitude)++[])) at formatted
  rw [outputStore] at formatted
  obtain ⟨finish,ran,halted,stored⟩ := parsedRun.sequence (selected.sequence (cleared.sequence formatted))
  refine ⟨parseTime+1+((1+(if sign then num.length+1 else 0))+1+(den.length+1+1+Normalize.formatCost magnitude)),finish,?_,⟨?_,halted⟩,?_⟩
  · have formatBound := Normalize.formatCost_le magnitude
    have magBound : magnitude.length ≤ num.length := by unfold magnitude; split <;> simp
    have selectBound : (if sign then num.length+1 else 0) ≤ num.length+1 := by split <;> omega
    have lengths := parsed_lengths input
    change num.length+den.length ≤ input.length at lengths
    change _ ≤ 50*(input.length+1)^1
    simp only [pow_one]
    omega
  · have start : initial numeratorToNatRoutine.program input = ⟨0,file input [] [] [] [] []⟩ := by
      apply congrArg (Config.mk _)
      funext r; fin_cases r <;> rfl
    rw [start]
    exact ran
  · rw [stored]
    change Encoding.natural.encode (Encoding.value magnitude) = Encoding.natural.encode (if sign then 0 else Encoding.value num)
    dsimp only [magnitude]
    cases sign <;> rfl

theorem numeratorNatural_rational (value : Rat) : numeratorNatural (Encoding.rational.encode value) = value.num.toNat := by
  have parsed := Pair.parsed_rational value []
  have signed := Pair.sign_rational value []
  simp only [List.append_nil] at parsed signed
  simp only [numeratorNatural,parsed,signed,Encoding.value_bits,Encoding.negative]
  generalize value.num = z
  cases z <;> simp

/-- The exact scalar guard used by `positiveIntegral?`; extraction is sound
only when both separately implemented tests accept. -/
theorem positiveIntegral_guard (value : Rat) :
    (Predicates.predicate .integral (Encoding.rational.encode value) &&
      Predicates.predicate .positive (Encoding.rational.encode value)) = true ↔
      value.den=1 ∧ 0<value.num := by
  rw [Predicates.integral_correct,Predicates.positive_correct]
  simp only [Bool.and_eq_true,decide_eq_true_eq,Rat.num_pos]

theorem positiveIntegral_conversion (value : Rat)
    (accepted : (Predicates.predicate .integral (Encoding.rational.encode value) &&
      Predicates.predicate .positive (Encoding.rational.encode value))=true) :
    0<numeratorNatural (Encoding.rational.encode value) ∧
      (numeratorNatural (Encoding.rational.encode value) : Rat)=value := by
  obtain ⟨integer,positive⟩ := (positiveIntegral_guard value).mp accepted
  rw [numeratorNatural_rational]
  constructor
  · omega
  · have cast : (value.num.toNat : Int) = value.num := Int.toNat_of_nonneg (by omega)
    calc
      (value.num.toNat : Rat) = (value.num : Rat) := by exact_mod_cast cast
      _ = value := Rat.coe_int_num_of_den_eq_one integer

end Counting.StackMachine.RationalArithmetic
