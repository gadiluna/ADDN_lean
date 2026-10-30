import Counting.StackRationalToNat

namespace Counting.StackMachine.RationalArithmetic.Predicates
open Routine

abbrev guardedIntegral : Routine 14 := EncodingPrograms.branchRoutine 2 (test .integral) (pushBit 2 false)
abbrev positiveIntegralRoutine : Routine 14 := sequence rationalParser
  (sequence (test .positive) (sequence guardedIntegral output))
def positiveIntegralPredicate (input : List Bool) : Bool := predicate .positive input && predicate .integral input

theorem integral_emptySign_executes (num den : List Bool) :
    Executes (test .integral) (file num den [] [] [] []) (testCost .integral den false)
      (file num (denAfter .integral den) [check .integral num den false] [] [] []) := by
  refine ⟨⟨7,_⟩,?_,rfl,rfl⟩
  cases den with
  | nil => apply congrArg some; apply congrArg (Config.mk _); funext r; fin_cases r <;> rfl
  | cons bit rest =>
    cases bit
    · apply congrArg some; apply congrArg (Config.mk _); funext r; fin_cases r <;> rfl
    · cases rest with
      | nil => apply congrArg some; apply congrArg (Config.mk _); funext r; fin_cases r <;> rfl
      | cons bit rest =>
        cases bit <;> apply congrArg some <;> apply congrArg (Config.mk _)
        all_goals funext r; fin_cases r <;> rfl

theorem guardedIntegral_executes (num den : List Bool) (flag : Bool) :
    Executes guardedIntegral (file num den [flag] [] [] [])
      (1+(if flag then testCost .integral den false else 1))
      (file num (if flag then denAfter .integral den else den)
        [flag && check .integral num den false] [] [] []) := by
  have reset : Function.update (file num den [flag] [] [] []) 2 [] = file num den [] [] [] [] := by
    funext r; fin_cases r <;> simp [file]
  apply Signed.branch_bit 2 (test .integral) (pushBit 2 false) _ _ flag _ rfl
  rw [reset]
  cases flag
  · have emitted := pushBit_executes (registers := 14) 2 false (file num den [] [] [] [])
    have result : Function.update (file num den [] [] [] []) 2 [false] = file num den [false] [] [] [] := by
      funext r; fin_cases r <;> simp [file]
    change Executes _ _ 1 (Function.update (file num den [] [] [] []) 2 [false]) at emitted
    rw [result] at emitted
    exact emitted
  · exact integral_emptySign_executes num den

theorem positiveIntegral_computes : ComputesIn positiveIntegralRoutine.program
    (fun input => Encoding.boolean.encode (positiveIntegralPredicate input)) (Complexity.polynomial 60 1) := by
  intro input
  let num := (parsed input).first
  let den := (parsed input).second
  let sign := parsedSign input
  let reduced := numAfter .positive num sign
  let flag := check .positive num den sign
  let remaining := if flag then denAfter .integral den else den
  obtain ⟨parseTime,parseBound,parsedRun⟩ := rationalParser_executes input
  have positive := test_executes .positive num den sign
  change Executes (test .positive) _ (testCost .positive den sign) (file reduced den [flag] [] [] []) at positive
  have integral := guardedIntegral_executes reduced den flag
  have finished := output_executes reduced remaining [] (flag && check .integral reduced den false)
  obtain ⟨finish,ran,halted,stored⟩ := parsedRun.sequence (positive.sequence (integral.sequence finished))
  refine ⟨parseTime+1+(testCost .positive den sign+1+(1+(if flag then testCost .integral den false else 1)+1+(remaining.length+12))),finish,?_,⟨?_,halted⟩,?_⟩
  · have firstCost := testCost_le .positive den sign
    have secondCost := testCost_le .integral den false
    have branchCost : (if flag then testCost .integral den false else 1) ≤ 3 := by split <;> omega
    have remainingBound : remaining.length ≤ den.length := by
      unfold remaining
      split
      · exact denAfter_length .integral den
      · rfl
    have lengths := parsed_lengths input
    change num.length+den.length ≤ input.length at lengths
    change _ ≤ 60*(input.length+1)^1
    simp only [pow_one]
    omega
  · have start : initial positiveIntegralRoutine.program input = ⟨0,file input [] [] [] [] []⟩ := by
      apply congrArg (Config.mk _)
      funext r; fin_cases r <;> rfl
    rw [start]
    exact ran
  · rw [stored]
    rfl

theorem positiveIntegral_correct (value : Rat) :
    positiveIntegralPredicate (Encoding.rational.encode value) = decide (value.den=1 ∧ 0<value.num) := by
  simp only [positiveIntegralPredicate,positive_correct,integral_correct]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true,decide_eq_true_eq]
  rw [← Rat.num_pos,and_comm]

end Counting.StackMachine.RationalArithmetic.Predicates
