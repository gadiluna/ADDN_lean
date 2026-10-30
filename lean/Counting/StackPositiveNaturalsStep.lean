import Counting.StackPositiveNaturalsCall
import Counting.PositiveNaturalsSpec
import Counting.StackRowScaleStep
import Counting.StackBooleanFold

namespace Counting.StackMachine.PositiveNaturals
open Routine

def callRoles : Fin 20 ↪ Fin 32 := ⟨![4,5,7,24,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23],by decide⟩
abbrev callItem (scalar : Routine 14) : Routine 30 := relocate (PositiveNaturalsCall.invoke scalar) callRoles
abbrev testItem : Routine 30 := callItem RationalArithmetic.Predicates.positiveIntegralRoutine
abbrev extractItem : Routine 30 := callItem RationalArithmetic.numeratorToNatRoutine
abbrev combineStatus : Routine 30 := BooleanFold.single .conjunction 5 28
abbrev emitItem : Routine 30 := sequence (clear 4) (ofProgram (ListPrograms.reverseProgram 30 5 2))
abbrev body : Routine 30 := sequence RowScale.readItem
  (sequence testItem (sequence combineStatus (sequence extractItem emitItem)))

theorem callItem_executes (scalar : Routine 14) (function : List Bool → List Bool)
    (bound : Nat → Nat) (computes : ComputesIn scalar.program function bound)
    (input reversed counter item header status : List Bool) :
    ∃ time ≤ 30*(bound item.length+item.length+3),
      Executes (callItem scalar) (RowScale.file [] input reversed counter item [] header status []) time
        (RowScale.file [] input reversed counter item (function item) header status []) := by
  obtain ⟨time,bounded,ran⟩ := PositiveNaturalsCall.invoke_executes scalar function bound computes item
  refine ⟨time,bounded,?_⟩
  apply relocate_executes_frame (PositiveNaturalsCall.invoke scalar) callRoles _ _ _ _ time _ _ _ ran
  · funext r; fin_cases r <;> simp [RowScale.file,PositiveNaturalsCall.file,callRoles]
  · intro r; fin_cases r <;> simp [RowScale.file,PositiveNaturalsCall.file,callRoles]
  · intro r outside
    fin_cases r
    · simp [RowScale.file]
    · simp [RowScale.file]
    · simp [RowScale.file]
    · simp [RowScale.file]
    · simp [RowScale.file]
    · exact False.elim (outside 1 rfl)
    all_goals simp [RowScale.file]

theorem testItem_executes (value : Rat) (input reversed counter header status : List Bool) :
    ∃ time ≤ 2000*((Encoding.rational.encode value).length+1),
      Executes testItem (RowScale.file [] input reversed counter (Encoding.rational.encode value) [] header status []) time
        (RowScale.file [] input reversed counter (Encoding.rational.encode value) [Counting.PositiveNaturals.guard value] header status []) := by
  obtain ⟨time,bounded,ran⟩ := callItem_executes RationalArithmetic.Predicates.positiveIntegralRoutine
    _ _ RationalArithmetic.Predicates.positiveIntegral_computes input reversed counter
    (Encoding.rational.encode value) header status
  change Executes testItem _ time
    (RowScale.file [] input reversed counter (Encoding.rational.encode value)
      [RationalArithmetic.Predicates.positiveIntegralPredicate (Encoding.rational.encode value)] header status []) at ran
  rw [Counting.PositiveNaturals.guard_scalar] at ran
  refine ⟨time,bounded.trans ?_,ran⟩
  simp only [Complexity.polynomial,pow_one]
  omega

theorem extractItem_executes (value : Rat) (input reversed counter header status : List Bool) :
    ∃ time ≤ 2000*((Encoding.rational.encode value).length+1),
      Executes extractItem (RowScale.file [] input reversed counter (Encoding.rational.encode value) [] header status []) time
        (RowScale.file [] input reversed counter (Encoding.rational.encode value)
          (Encoding.natural.encode value.num.toNat) header status []) := by
  obtain ⟨time,bounded,ran⟩ := callItem_executes RationalArithmetic.numeratorToNatRoutine
    _ _ RationalArithmetic.numeratorToNat_computes input reversed counter (Encoding.rational.encode value) header status
  change Executes extractItem _ time (RowScale.file [] input reversed counter (Encoding.rational.encode value)
    (Encoding.natural.encode (RationalArithmetic.numeratorNatural (Encoding.rational.encode value))) header status []) at ran
  rw [RationalArithmetic.numeratorNatural_rational] at ran
  refine ⟨time,bounded.trans ?_,ran⟩
  simp only [Complexity.polynomial,pow_one]
  omega

theorem combineStatus_executes (input reversed counter item header : List Bool) (accepted guard : Bool) :
    Executes combineStatus (RowScale.file [] input reversed counter item [guard] header [accepted] []) 3
      (RowScale.file [] input reversed counter item [] header [accepted && guard] []) := by
  have ran := BooleanFold.single_executes .conjunction (5:Fin 32) 28 (by decide)
    (RowScale.file [] input reversed counter item [guard] header [accepted] []) guard accepted [] [] rfl rfl
  have result : BooleanFold.updated 5 28 (RowScale.file [] input reversed counter item [guard] header [accepted] []) []
      (BooleanFold.operation .conjunction accepted guard) [] =
      RowScale.file [] input reversed counter item [] header [accepted && guard] [] := by
    funext r; fin_cases r <;> simp [BooleanFold.updated,RowScale.file,BooleanFold.operation]
  rw [result] at ran
  exact ran

theorem emitItem_executes (input reversed counter item header status result : List Bool) :
    Executes emitItem (RowScale.file [] input reversed counter item result header status [])
      (item.length+2*result.length+3)
      (RowScale.file [] input (result.reverse++reversed) counter [] [] header status []) := by
  have cleared := clear_executes (registers := 30) 4 (RowScale.file [] input reversed counter item result header status [])
  have clearStore : Function.update (RowScale.file [] input reversed counter item result header status []) 4 [] =
      RowScale.file [] input reversed counter [] result header status [] := by
    funext r; fin_cases r <;> simp [RowScale.file]
  change Executes (clear 4) _ (item.length+1)
    (Function.update (RowScale.file [] input reversed counter item result header status []) 4 []) at cleared
  rw [clearStore] at cleared
  have reversedRun := reverse_executes 30 5 2 (by decide) (RowScale.file [] input reversed counter [] result header status [])
  have reverseStore : Function.update (Function.update (RowScale.file [] input reversed counter [] result header status []) 5 [])
      2 (result.reverse++reversed) = RowScale.file [] input (result.reverse++reversed) counter [] [] header status [] := by
    funext r; fin_cases r <;> simp [RowScale.file]
  change Executes _ _ (2*result.length+1)
    (Function.update (Function.update (RowScale.file [] input reversed counter [] result header status []) 5 [])
      2 (result.reverse++reversed)) at reversedRun
  rw [reverseStore] at reversedRun
  convert cleared.sequence reversedRun using 1
  omega

theorem body_executes (value : Rat) (suffix reversed counter header : List Bool) (accepted : Bool) :
    ∃ time ≤ 5000*((Encoding.rational.encode value).length+1),
      Executes body
        (RowScale.file [] (Encoding.frame (Encoding.rational.encode value)++suffix) reversed counter [] [] header [accepted] []) time
        (RowScale.file [] suffix ((Encoding.natural.encode value.num.toNat).reverse++reversed) counter [] [] header
          [accepted && Counting.PositiveNaturals.guard value] []) := by
  have parsed := RowScale.readItem_executes [] (Encoding.rational.encode value) suffix reversed counter header [accepted]
  obtain ⟨testTime,testBound,testRun⟩ := testItem_executes value suffix reversed counter header [accepted]
  have combined := combineStatus_executes suffix reversed counter (Encoding.rational.encode value) header accepted (Counting.PositiveNaturals.guard value)
  obtain ⟨extractTime,extractBound,extractRun⟩ := extractItem_executes value suffix reversed counter header
    [accepted && Counting.PositiveNaturals.guard value]
  have emitted := emitItem_executes suffix reversed counter (Encoding.rational.encode value) header
    [accepted && Counting.PositiveNaturals.guard value] (Encoding.natural.encode value.num.toNat)
  refine ⟨_,?_,parsed.sequence (testRun.sequence (combined.sequence (extractRun.sequence emitted)))⟩
  have outputLength := Counting.PositiveNaturals.numerator_length value
  omega

end Counting.StackMachine.PositiveNaturals
