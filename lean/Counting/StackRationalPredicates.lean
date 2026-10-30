import Counting.StackRationalEncoding
import Counting.StackRationalPairSpec

namespace Counting.StackMachine.RationalArithmetic.Predicates
open Routine

inductive Kind where
  | zero | negative | positive | integral
  deriving DecidableEq

def check : Kind → List Bool → List Bool → Bool → Bool
  | .zero, numerator, _, _ => numerator.isEmpty
  | .negative, _, _, sign => sign
  | .positive, numerator, _, sign => !sign && !numerator.isEmpty
  | .integral, _, denominator, _ => denominator == [true]

def numAfter (kind : Kind) (num : List Bool) (sign : Bool) : List Bool :=
  if kind=.zero ∨ (kind=.positive ∧ sign=false) then num.tail else num

def denAfter (kind : Kind) (den : List Bool) : List Bool :=
  if kind=.integral then if den.headD false then den.tail.tail else den.tail else den

def signAfter (kind : Kind) (sign : Bool) : List Bool :=
  if kind=.negative ∨ kind=.positive then [] else [sign]

def test (kind : Kind) : Routine 14 where
  states := 7
  code state := match state.val with
    | 0 => match kind with
      | .zero => .pop 0 5 6 6
      | .negative => .pop 5 6 6 5
      | .positive => .pop 5 2 2 6
      | .integral => .pop 1 6 6 3
    | 2 => .pop 0 6 5 5
    | 3 => .pop 1 5 6 6
    | 5 => .push 2 true 7
    | 6 => .push 2 false 7
    | _ => .halt

def testCost (kind : Kind) (den : List Bool) (sign : Bool) : Nat :=
  match kind with
  | .zero | .negative => 2
  | .positive => if sign then 2 else 3
  | .integral => if den.headD false then 3 else 2

theorem test_executes (kind : Kind) (num den : List Bool) (sign : Bool) :
    Executes (test kind) (file num den [] [] [] [sign]) (testCost kind den sign)
      (file (numAfter kind num sign) (denAfter kind den) [check kind num den sign] [] [] (signAfter kind sign)) := by
  refine ⟨⟨7,_⟩,?_,rfl,rfl⟩
  cases kind with
  | zero =>
    cases num with
    | nil => apply congrArg some; apply congrArg (Config.mk _); funext r; fin_cases r <;> rfl
    | cons bit rest =>
        cases bit <;> apply congrArg some <;> apply congrArg (Config.mk _)
        all_goals funext r; fin_cases r <;> rfl
  | negative =>
    cases sign <;> apply congrArg some <;> apply congrArg (Config.mk _)
    all_goals funext r; fin_cases r <;> rfl
  | positive =>
    cases sign
    · cases num with
      | nil => apply congrArg some; apply congrArg (Config.mk _); funext r; fin_cases r <;> rfl
      | cons bit rest =>
          cases bit <;> apply congrArg some <;> apply congrArg (Config.mk _)
          all_goals funext r; fin_cases r <;> rfl
    · apply congrArg some; apply congrArg (Config.mk _); funext r; fin_cases r <;> rfl
  | integral =>
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

theorem testCost_le (kind : Kind) (den : List Bool) (sign : Bool) : testCost kind den sign ≤ 3 := by
  cases kind <;> simp [testCost]
  · split <;> omega
  · split <;> omega

theorem denAfter_length (kind : Kind) (den : List Bool) : (denAfter kind den).length ≤ den.length := by
  unfold denAfter
  split
  · split
    · simp
      omega
    · simp
  · rfl

abbrev output : Routine 14 := sequence (clear 1) (move 13 2 1 7)
abbrev routine (kind : Kind) : Routine 14 := sequence rationalParser (sequence (test kind) output)
def predicate (kind : Kind) (input : List Bool) : Bool :=
  check kind (parsed input).first (parsed input).second (parsedSign input)

theorem output_executes (num den sign : List Bool) (flag : Bool) :
    Executes output (file num den [flag] [] [] sign) (den.length+12)
      (file num [flag] [] [] [] sign) := by
  have cleared := clear_executes (registers := 14) 1 (file num den [flag] [] [] sign)
  have clearStore : Function.update (file num den [flag] [] [] sign) 1 [] = file num [] [flag] [] [] sign := by
    funext r; fin_cases r <;> simp [file]
  change Executes (clear 1) _ (den.length+1) (Function.update (file num den [flag] [] [] sign) 1 []) at cleared
  rw [clearStore] at cleared
  have moved := move_executes 13 2 1 7 (by decide) (by decide) (by decide) (file num [] [flag] [] [] sign) rfl
  have moveStore : Function.update (Function.update (file num [] [flag] [] [] sign) 1 ([flag]++[])) 2 [] =
      file num [flag] [] [] [] sign := by
    funext r; fin_cases r <;> simp [file]
  change Executes (move 13 2 1 7) _ 10
    (Function.update (Function.update (file num [] [flag] [] [] sign) 1 ([flag]++[])) 2 []) at moved
  rw [moveStore] at moved
  convert cleared.sequence moved using 1

theorem predicate_computes (kind : Kind) : ComputesIn (routine kind).program
    (fun input => Encoding.boolean.encode (predicate kind input)) (Complexity.polynomial 50 1) := by
  intro input
  obtain ⟨parseTime,parseBound,parsedRun⟩ := rationalParser_executes input
  let num := (parsed input).first
  let den := (parsed input).second
  let sign := parsedSign input
  have tested := test_executes kind num den sign
  have formatted := output_executes (numAfter kind num sign) (denAfter kind den) (signAfter kind sign) (check kind num den sign)
  obtain ⟨finish,ran,halted,stored⟩ := parsedRun.sequence (tested.sequence formatted)
  refine ⟨parseTime+1+(testCost kind den sign+1+((denAfter kind den).length+12)),finish,?_,⟨?_,halted⟩,?_⟩
  · have cost := testCost_le kind den sign
    have remaining := denAfter_length kind den
    have lengths := parsed_lengths input
    change num.length+den.length ≤ input.length at lengths
    change _ ≤ 50*(input.length+1)^1
    simp only [pow_one]
    omega
  · have start : initial (routine kind).program input = ⟨0,file input [] [] [] [] []⟩ := by
      apply congrArg (Config.mk _)
      funext r; fin_cases r <;> rfl
    rw [start]
    exact ran
  · rw [stored]
    rfl

end Counting.StackMachine.RationalArithmetic.Predicates
