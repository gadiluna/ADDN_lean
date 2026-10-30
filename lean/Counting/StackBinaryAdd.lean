import Counting.StackArithmeticBits
import Counting.StackListPrograms

namespace Counting.StackMachine.Binary
open Arithmetic

/-- A generic full-adder loop on three distinct registers. Its output is
reversed; the subsequent reversal is an explicitly charged routine. -/
def addProgram (extra : Nat) (first second output : Fin (extra+3)) : Program where
  extraRegisters := extra+1
  states := 13
  code state := match state.val with
    | 0 => .pop first 2 3 4
    | 1 => .pop first 5 6 7
    | 2 => .pop second 13 8 9
    | 3 => .pop second 8 8 9
    | 4 => .pop second 9 9 10
    | 5 => .pop second 11 9 10
    | 6 => .pop second 9 9 10
    | 7 => .pop second 10 10 12
    | 8 => .push output false 0
    | 9 => .push output true 0
    | 10 => .push output false 1
    | 11 => .push output true 13
    | 12 => .push output true 1
    | _ => .halt

def addControl (extra : Nat) (first second output : Fin (extra+3)) (carry : Bool) :
    Control (addProgram extra first second output) := if carry then 1 else 0

def addConfig (extra : Nat) (first second output : Fin (extra+3))
    (state : Control (addProgram extra first second output))
    (base : Fin (extra+3) → List Bool) (a b result : List Bool) :
    Config (addProgram extra first second output) :=
  ⟨state, fun r => if r=first then a else if r=second then b else if r=output then result else base r⟩

theorem add_pair (extra : Nat) (first second output : Fin (extra+3))
    (fs : first ≠ second) (fo : first ≠ output) (so : second ≠ output)
    (base : Fin (extra+3) → List Bool) (carry a b : Bool) (as bs result : List Bool) :
    Machine.run (step (addProgram extra first second output)) 3
      (addConfig extra first second output (addControl extra first second output carry) base (a::as) (b::bs) result) =
      some (addConfig extra first second output (addControl extra first second output (carryBit carry a b))
        base as bs (sumBit carry a b::result)) := by
  have sf := Ne.symm fs
  have ofirst := Ne.symm fo
  have os := Ne.symm so
  cases carry <;> cases a <;> cases b <;>
    dsimp [Machine.run, step, addProgram, addConfig, addControl, carryBit, sumBit]
  all_goals
    simp_all
    refine ⟨rfl, ?_⟩
    funext r
    by_cases a : r=first
    · subst r; simp_all
    · by_cases b : r=second
      · subst r; simp_all
      · by_cases c : r=output
        · subst r; simp_all
        · simp_all

theorem add_left (extra : Nat) (first second output : Fin (extra+3))
    (fs : first ≠ second) (fo : first ≠ output) (so : second ≠ output)
    (base : Fin (extra+3) → List Bool) (carry a : Bool) (as result : List Bool) :
    Machine.run (step (addProgram extra first second output)) 3
      (addConfig extra first second output (addControl extra first second output carry) base (a::as) [] result) =
      some (addConfig extra first second output (addControl extra first second output (carryBit carry a false))
        base as [] (sumBit carry a false::result)) := by
  have sf := Ne.symm fs
  have ofirst := Ne.symm fo
  have os := Ne.symm so
  cases carry <;> cases a <;>
    dsimp [Machine.run, step, addProgram, addConfig, addControl, carryBit, sumBit]
  all_goals
    simp_all
    refine ⟨rfl, ?_⟩
    funext r
    by_cases a : r=first
    · subst r; simp_all
    · by_cases b : r=second
      · subst r; simp_all
      · by_cases c : r=output
        · subst r; simp_all
        · simp_all

theorem add_right (extra : Nat) (first second output : Fin (extra+3))
    (fs : first ≠ second) (fo : first ≠ output) (so : second ≠ output)
    (base : Fin (extra+3) → List Bool) (carry b : Bool) (bs result : List Bool) :
    Machine.run (step (addProgram extra first second output)) 3
      (addConfig extra first second output (addControl extra first second output carry) base [] (b::bs) result) =
      some (addConfig extra first second output (addControl extra first second output (carryBit carry false b))
        base [] bs (sumBit carry false b::result)) := by
  have sf := Ne.symm fs
  have ofirst := Ne.symm fo
  have os := Ne.symm so
  cases carry <;> cases b <;>
    dsimp [Machine.run, step, addProgram, addConfig, addControl, carryBit, sumBit]
  all_goals
    simp_all
    refine ⟨rfl, ?_⟩
    funext r
    by_cases a : r=first
    · subst r; simp_all
    · by_cases b : r=second
      · subst r; simp_all
      · by_cases c : r=output
        · subst r; simp_all
        · simp_all

theorem add_empty (extra : Nat) (first second output : Fin (extra+3))
    (fs : first ≠ second) (fo : first ≠ output) (so : second ≠ output)
    (base : Fin (extra+3) → List Bool) (carry : Bool) (result : List Bool) :
    Machine.run (step (addProgram extra first second output)) (if carry then 3 else 2)
      (addConfig extra first second output (addControl extra first second output carry) base [] [] result) =
      some (addConfig extra first second output 13 base [] [] ((addBits carry [] []).reverse++result)) := by
  have sf := Ne.symm fs
  have ofirst := Ne.symm fo
  have os := Ne.symm so
  cases carry <;>
    dsimp [Machine.run, step, addProgram, addConfig, addControl, addBits]
  all_goals
    simp_all [addBits]
  all_goals
    refine ⟨rfl, ?_⟩
    funext r
    by_cases a : r=first
    · subst r; simp_all
    · by_cases b : r=second
      · subst r; simp_all
      · by_cases c : r=output
        · subst r; simp_all
        · simp_all

/-- General carry propagation, preserving every unrelated register. -/
theorem add_run (extra : Nat) (first second output : Fin (extra+3))
    (fs : first ≠ second) (fo : first ≠ output) (so : second ≠ output)
    (base : Fin (extra+3) → List Bool) (carry : Bool) (a b result : List Bool) :
    ∃ transitions ≤ 3*(a.length+b.length)+3,
      Machine.run (step (addProgram extra first second output)) transitions
        (addConfig extra first second output (addControl extra first second output carry) base a b result) =
        some (addConfig extra first second output 13 base [] [] ((addBits carry a b).reverse++result)) := by
  induction a generalizing carry b result with
  | nil =>
      induction b generalizing carry result with
      | nil =>
          refine ⟨if carry then 3 else 2, ?_, add_empty _ _ _ _ fs fo so base carry result⟩
          cases carry <;> simp
      | cons b bs ih =>
          obtain ⟨transitions, bounded, executed⟩ := ih (carryBit carry false b) (sumBit carry false b::result)
          refine ⟨3+transitions, by simp only [List.length_cons, List.length_nil] at *; omega, ?_⟩
          rw [Machine.run_add, add_right _ _ _ _ fs fo so, Option.bind_some, executed]
          simp only [addBits, List.reverse_cons, List.append_assoc, List.singleton_append]
  | cons a as ih =>
      cases b with
      | nil =>
          obtain ⟨transitions, bounded, executed⟩ := ih (carryBit carry a false) [] (sumBit carry a false::result)
          refine ⟨3+transitions, by simp only [List.length_cons, List.length_nil] at *; omega, ?_⟩
          rw [Machine.run_add, add_left _ _ _ _ fs fo so, Option.bind_some, executed]
          simp only [addBits, List.reverse_cons, List.append_assoc, List.singleton_append]
      | cons b bs =>
          obtain ⟨transitions, bounded, executed⟩ := ih (carryBit carry a b) bs (sumBit carry a b::result)
          refine ⟨3+transitions, by simp only [List.length_cons] at *; omega, ?_⟩
          rw [Machine.run_add, add_pair _ _ _ _ fs fo so, Option.bind_some, executed]
          simp only [addBits, List.reverse_cons, List.append_assoc, List.singleton_append]

theorem add_halted (extra : Nat) (first second output : Fin (extra+3))
    (base : Fin (extra+3) → List Bool) (a b result : List Bool) :
    step (addProgram extra first second output) (addConfig extra first second output 13 base a b result) = none := rfl

end Counting.StackMachine.Binary
