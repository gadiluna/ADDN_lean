import Counting.StackBinaryCompareBits
import Counting.StackRoutineLists

namespace Counting.StackMachine.Binary

/-- Destructive numeric comparison of arbitrary little-endian bit strings.
Missing columns are zero, including noncanonical leading zeroes. -/
def compareProgram (extra : Nat) (first second output : Fin (extra+3)) : Program where
  extraRegisters := extra+1
  states := 10
  code state := match state.val with
    | 0 => .pop first 6 2 4
    | 1 => .pop first 7 3 5
    | 2 => .pop second 0 0 0
    | 3 => .pop second 1 1 0
    | 4 => .pop second 1 1 0
    | 5 => .pop second 1 1 1
    | 6 => .pop second 9 0 0
    | 7 => .pop second 8 1 0
    | 8 => .push output false 10
    | 9 => .push output true 10
    | _ => .halt

def compareControl (extra : Nat) (first second output : Fin (extra+3)) (previous : Bool) :
    Control (compareProgram extra first second output) := if previous then 0 else 1

def compareConfig (extra : Nat) (first second output : Fin (extra+3))
    (state : Control (compareProgram extra first second output))
    (base : Fin (extra+3) → List Bool) (a b result : List Bool) :
    Config (compareProgram extra first second output) :=
  ⟨state, fun r => if r=first then a else if r=second then b else if r=output then result else base r⟩

theorem compare_pair (extra : Nat) (first second output : Fin (extra+3))
    (fs : first ≠ second) (fo : first ≠ output) (so : second ≠ output)
    (base : Fin (extra+3) → List Bool) (previous a b : Bool) (as bs result : List Bool) :
    Machine.run (step (compareProgram extra first second output)) 2
      (compareConfig extra first second output (compareControl extra first second output previous) base (a::as) (b::bs) result) =
      some (compareConfig extra first second output (compareControl extra first second output (Machine.compareColumn previous a b))
        base as bs result) := by
  have sf := Ne.symm fs
  have ofirst := Ne.symm fo
  have os := Ne.symm so
  cases previous <;> cases a <;> cases b <;>
    dsimp [Machine.run, step, compareProgram, compareConfig, compareControl, Machine.compareColumn]
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

theorem compare_left (extra : Nat) (first second output : Fin (extra+3))
    (fs : first ≠ second) (fo : first ≠ output) (so : second ≠ output)
    (base : Fin (extra+3) → List Bool) (previous a : Bool) (as result : List Bool) :
    Machine.run (step (compareProgram extra first second output)) 2
      (compareConfig extra first second output (compareControl extra first second output previous) base (a::as) [] result) =
      some (compareConfig extra first second output (compareControl extra first second output (Machine.compareColumn previous a false))
        base as [] result) := by
  have sf := Ne.symm fs
  have ofirst := Ne.symm fo
  have os := Ne.symm so
  cases previous <;> cases a <;>
    dsimp [Machine.run, step, compareProgram, compareConfig, compareControl, Machine.compareColumn]
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

theorem compare_right (extra : Nat) (first second output : Fin (extra+3))
    (fs : first ≠ second) (fo : first ≠ output) (so : second ≠ output)
    (base : Fin (extra+3) → List Bool) (previous b : Bool) (bs result : List Bool) :
    Machine.run (step (compareProgram extra first second output)) 2
      (compareConfig extra first second output (compareControl extra first second output previous) base [] (b::bs) result) =
      some (compareConfig extra first second output (compareControl extra first second output (Machine.compareColumn previous false b))
        base [] bs result) := by
  have sf := Ne.symm fs
  have ofirst := Ne.symm fo
  have os := Ne.symm so
  cases previous <;> cases b <;>
    dsimp [Machine.run, step, compareProgram, compareConfig, compareControl, Machine.compareColumn]
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

theorem compare_empty (extra : Nat) (first second output : Fin (extra+3))
    (fs : first ≠ second) (fo : first ≠ output) (so : second ≠ output)
    (base : Fin (extra+3) → List Bool) (previous : Bool) (result : List Bool) :
    Machine.run (step (compareProgram extra first second output)) 3
      (compareConfig extra first second output (compareControl extra first second output previous) base [] [] result) =
      some (compareConfig extra first second output 10 base [] [] (previous::result)) := by
  have sf := Ne.symm fs
  have ofirst := Ne.symm fo
  have os := Ne.symm so
  cases previous <;> dsimp [Machine.run,step,compareProgram,compareConfig,compareControl]
  all_goals
    simp_all
    refine ⟨rfl,?_⟩
    funext r
    by_cases a : r=first
    · subst r; simp_all
    · by_cases b : r=second
      · subst r; simp_all
      · by_cases c : r=output
        · subst r; simp_all
        · simp_all

/-- Exactly two instructions per column and three for final output. -/
theorem compare_run (extra : Nat) (first second output : Fin (extra+3))
    (fs : first ≠ second) (fo : first ≠ output) (so : second ≠ output)
    (base : Fin (extra+3) → List Bool) (previous : Bool) (a b result : List Bool) :
    Machine.run (step (compareProgram extra first second output)) (2*max a.length b.length+3)
      (compareConfig extra first second output (compareControl extra first second output previous) base a b result) =
      some (compareConfig extra first second output 10 base [] [] (compareBits previous a b::result)) := by
  induction a generalizing previous b with
  | nil =>
      induction b generalizing previous with
      | nil => simpa only [List.length_nil,Nat.zero_max,Nat.mul_zero,Nat.zero_add,compareBits] using
          compare_empty _ _ _ _ fs fo so base previous result
      | cons b bs ih =>
          have time : 2*max (([] : List Bool).length) (b::bs).length+3 = 2+(2*max (([] : List Bool).length) bs.length+3) := by simp; omega
          rw [time,Machine.run_add,compare_right _ _ _ _ fs fo so,Option.bind_some,ih]
          simp only [compareBits]
  | cons a as ih =>
      cases b with
      | nil =>
          have time : 2*max (a::as).length (([] : List Bool).length)+3 = 2+(2*max as.length (([] : List Bool).length)+3) := by simp; omega
          rw [time,Machine.run_add,compare_left _ _ _ _ fs fo so,Option.bind_some,ih]
          simp only [compareBits]
      | cons b bs =>
          have time : 2*max (a::as).length (b::bs).length+3 = 2+(2*max as.length bs.length+3) := by
            simp only [List.length_cons]
            omega
          rw [time,Machine.run_add,compare_pair _ _ _ _ fs fo so,Option.bind_some,ih]
          simp only [compareBits]

theorem compare_halted (extra : Nat) (first second output : Fin (extra+3))
    (base : Fin (extra+3) → List Bool) (a b result : List Bool) :
    step (compareProgram extra first second output) (compareConfig extra first second output 10 base a b result) = none := rfl

end Counting.StackMachine.Binary
