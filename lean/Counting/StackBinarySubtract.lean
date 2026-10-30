import Counting.StackBinarySubtractBits
import Counting.StackRoutineLists

namespace Counting.StackMachine.Binary

/-- A full-subtractor loop. It halts on either final borrow and emits the
fixed-width difference in reverse order; overflow is tracked by its final
control state, so no implicit assumption of ordered operands is made. -/
def subtractProgram (extra : Nat) (first second output : Fin (extra+3)) : Program where
  extraRegisters := extra+1
  states := 13
  code state := match state.val with
    | 0 => .pop first 2 3 4
    | 1 => .pop first 5 6 7
    | 2 => .pop second 12 8 11
    | 3 => .pop second 8 8 11
    | 4 => .pop second 9 9 8
    | 5 => .pop second 13 11 10
    | 6 => .pop second 11 11 10
    | 7 => .pop second 8 8 11
    | 8 => .push output false 0
    | 9 => .push output true 0
    | 10 => .push output false 1
    | 11 => .push output true 1
    | _ => .halt

def subtractControl (extra : Nat) (first second output : Fin (extra+3)) (borrow : Bool) :
    Control (subtractProgram extra first second output) := if borrow then 1 else 0

def subtractEnd (extra : Nat) (first second output : Fin (extra+3)) (borrow : Bool) :
    Control (subtractProgram extra first second output) := if borrow then 13 else 12

def subtractConfig (extra : Nat) (first second output : Fin (extra+3))
    (state : Control (subtractProgram extra first second output))
    (base : Fin (extra+3) → List Bool) (a b result : List Bool) :
    Config (subtractProgram extra first second output) :=
  ⟨state, fun r => if r=first then a else if r=second then b else if r=output then result else base r⟩

theorem subtract_pair (extra : Nat) (first second output : Fin (extra+3))
    (fs : first ≠ second) (fo : first ≠ output) (so : second ≠ output)
    (base : Fin (extra+3) → List Bool) (borrow a b : Bool) (as bs result : List Bool) :
    Machine.run (step (subtractProgram extra first second output)) 3
      (subtractConfig extra first second output (subtractControl extra first second output borrow) base (a::as) (b::bs) result) =
      some (subtractConfig extra first second output (subtractControl extra first second output (borrowBit borrow a b))
        base as bs (differenceBit borrow a b::result)) := by
  have sf := Ne.symm fs
  have ofirst := Ne.symm fo
  have os := Ne.symm so
  cases borrow <;> cases a <;> cases b <;>
    dsimp [Machine.run, step, subtractProgram, subtractConfig, subtractControl, borrowBit, differenceBit]
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

theorem subtract_left (extra : Nat) (first second output : Fin (extra+3))
    (fs : first ≠ second) (fo : first ≠ output) (so : second ≠ output)
    (base : Fin (extra+3) → List Bool) (borrow a : Bool) (as result : List Bool) :
    Machine.run (step (subtractProgram extra first second output)) 3
      (subtractConfig extra first second output (subtractControl extra first second output borrow) base (a::as) [] result) =
      some (subtractConfig extra first second output (subtractControl extra first second output (borrowBit borrow a false))
        base as [] (differenceBit borrow a false::result)) := by
  have sf := Ne.symm fs
  have ofirst := Ne.symm fo
  have os := Ne.symm so
  cases borrow <;> cases a <;>
    dsimp [Machine.run, step, subtractProgram, subtractConfig, subtractControl, borrowBit, differenceBit]
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

theorem subtract_right (extra : Nat) (first second output : Fin (extra+3))
    (fs : first ≠ second) (fo : first ≠ output) (so : second ≠ output)
    (base : Fin (extra+3) → List Bool) (borrow b : Bool) (bs result : List Bool) :
    Machine.run (step (subtractProgram extra first second output)) 3
      (subtractConfig extra first second output (subtractControl extra first second output borrow) base [] (b::bs) result) =
      some (subtractConfig extra first second output (subtractControl extra first second output (borrowBit borrow false b))
        base [] bs (differenceBit borrow false b::result)) := by
  have sf := Ne.symm fs
  have ofirst := Ne.symm fo
  have os := Ne.symm so
  cases borrow <;> cases b <;>
    dsimp [Machine.run, step, subtractProgram, subtractConfig, subtractControl, borrowBit, differenceBit]
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

theorem subtract_empty (extra : Nat) (first second output : Fin (extra+3))
    (fs : first ≠ second)
    (base : Fin (extra+3) → List Bool) (borrow : Bool) (result : List Bool) :
    Machine.run (step (subtractProgram extra first second output)) 2
      (subtractConfig extra first second output (subtractControl extra first second output borrow) base [] [] result) =
      some (subtractConfig extra first second output (subtractEnd extra first second output borrow) base [] [] result) := by
  cases borrow <;> simp [Machine.run,step,subtractProgram,subtractConfig,subtractControl,subtractEnd,Ne.symm fs] <;> rfl

/-- Exact linear termination for all bit strings, including underflow. -/
theorem subtract_run (extra : Nat) (first second output : Fin (extra+3))
    (fs : first ≠ second) (fo : first ≠ output) (so : second ≠ output)
    (base : Fin (extra+3) → List Bool) (borrow : Bool) (a b result : List Bool) :
    Machine.run (step (subtractProgram extra first second output)) (3*max a.length b.length+2)
      (subtractConfig extra first second output (subtractControl extra first second output borrow) base a b result) =
      some (subtractConfig extra first second output (subtractEnd extra first second output (subtractBits borrow a b).2)
        base [] [] ((subtractBits borrow a b).1.reverse++result)) := by
  induction a generalizing borrow b result with
  | nil =>
      induction b generalizing borrow result with
      | nil => simpa only [List.length_nil,Nat.zero_max,Nat.mul_zero,Nat.zero_add,subtractBits,List.reverse_nil,List.nil_append] using
          subtract_empty _ _ _ _ fs base borrow result
      | cons b bs ih =>
          have time : 3*max (([] : List Bool).length) (b::bs).length+2 = 3+(3*max (([] : List Bool).length) bs.length+2) := by simp; omega
          rw [time,Machine.run_add,subtract_right _ _ _ _ fs fo so,Option.bind_some,ih]
          simp only [subtractBits,List.reverse_cons,List.append_assoc,List.singleton_append]
  | cons a as ih =>
      cases b with
      | nil =>
          have time : 3*max (a::as).length (([] : List Bool).length)+2 = 3+(3*max as.length (([] : List Bool).length)+2) := by simp; omega
          rw [time,Machine.run_add,subtract_left _ _ _ _ fs fo so,Option.bind_some,ih]
          simp only [subtractBits,List.reverse_cons,List.append_assoc,List.singleton_append]
      | cons b bs =>
          have time : 3*max (a::as).length (b::bs).length+2 = 3+(3*max as.length bs.length+2) := by
            simp only [List.length_cons]
            omega
          rw [time,Machine.run_add,subtract_pair _ _ _ _ fs fo so,Option.bind_some,ih]
          simp only [subtractBits,List.reverse_cons,List.append_assoc,List.singleton_append]

theorem subtract_halted (extra : Nat) (first second output : Fin (extra+3))
    (base : Fin (extra+3) → List Bool) (borrow : Bool) (a b result : List Bool) :
    step (subtractProgram extra first second output)
      (subtractConfig extra first second output (subtractEnd extra first second output borrow) base a b result) = none := by
  cases borrow <;> rfl

end Counting.StackMachine.Binary
