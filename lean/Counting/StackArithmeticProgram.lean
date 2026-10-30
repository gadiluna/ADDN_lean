import Counting.StackArithmeticBits

namespace Counting.StackMachine.Arithmetic

/-- Addition on the repository's framed natural-pair representation. The
finite stack code parses two frames, restores little-endian stack order,
adds with carry, removes high zeroes, and emits the natural-number frame.
The parser sends incomplete frames to the explicit zero-output branch.
Correctness and transition bounds are established phase by phase below. -/
def additionProgram : Program where
  extraRegisters := 5
  states := 41
  code state := match state.val with
    | 0 => .pop 0 40 5 1
    | 1 => .pop 0 40 2 3
    | 2 => .push 2 false 0
    | 3 => .push 2 true 0
    | 5 => .pop 0 40 10 6
    | 6 => .pop 0 40 7 8
    | 7 => .push 3 false 5
    | 8 => .push 3 true 5
    | 10 => .pop 2 14 11 12
    | 11 => .push 4 false 10
    | 12 => .push 4 true 10
    | 14 => .pop 3 18 15 16
    | 15 => .push 5 false 14
    | 16 => .push 5 true 14
    | 18 => .pop 4 20 21 22
    | 19 => .pop 4 23 24 25
    | 20 => .pop 5 34 26 27
    | 21 => .pop 5 26 26 27
    | 22 => .pop 5 27 27 28
    | 23 => .pop 5 29 27 28
    | 24 => .pop 5 27 27 28
    | 25 => .pop 5 28 28 30
    | 26 => .push 6 false 18
    | 27 => .push 6 true 18
    | 28 => .push 6 false 19
    | 29 => .push 6 true 34
    | 30 => .push 6 true 19
    | 34 => .push 1 false 35
    | 35 => .pop 6 41 35 36
    | 36 => .push 1 true 38
    | 37 => .push 1 false 38
    | 38 => .push 1 true 39
    | 39 => .pop 6 41 37 36
    | 40 => .push 1 false 41
    | _ => .halt

def carryControl (carry : Bool) : Control additionProgram := if carry then 19 else 18

/-- A concrete addition phase keeps the other four registers unchanged. -/
def addConfig (state : Control additionProgram) (base : Register additionProgram → List Bool)
    (first second result : List Bool) : Config additionProgram :=
  ⟨state, fun r => if r = 4 then first else if r = 5 then second else if r = 6 then result else base r⟩

theorem add_pair (carry a b : Bool) (first second result : List Bool)
    (base : Register additionProgram → List Bool) :
    Machine.run (step additionProgram) 3
      (addConfig (carryControl carry) base (a::first) (b::second) result) =
      some (addConfig (carryControl (carryBit carry a b)) base first second
        (sumBit carry a b :: result)) := by
  cases carry <;> cases a <;> cases b <;>
    apply congrArg some <;> apply congrArg (Config.mk _) <;>
      funext r <;> fin_cases r <;> rfl

theorem add_left (carry a : Bool) (first result : List Bool)
    (base : Register additionProgram → List Bool) :
    Machine.run (step additionProgram) 3
      (addConfig (carryControl carry) base (a::first) [] result) =
      some (addConfig (carryControl (carryBit carry a false)) base first []
        (sumBit carry a false :: result)) := by
  cases carry <;> cases a <;>
    apply congrArg some <;> apply congrArg (Config.mk _) <;>
      funext r <;> fin_cases r <;> rfl

theorem add_right (carry b : Bool) (second result : List Bool)
    (base : Register additionProgram → List Bool) :
    Machine.run (step additionProgram) 3
      (addConfig (carryControl carry) base [] (b::second) result) =
      some (addConfig (carryControl (carryBit carry false b)) base [] second
        (sumBit carry false b :: result)) := by
  cases carry <;> cases b <;>
    apply congrArg some <;> apply congrArg (Config.mk _) <;>
      funext r <;> fin_cases r <;> rfl

theorem add_empty (carry : Bool) (result : List Bool) (base : Register additionProgram → List Bool) :
    Machine.run (step additionProgram) (if carry then 3 else 2)
      (addConfig (carryControl carry) base [] [] result) =
      some (addConfig 34 base [] [] ((addBits carry [] []).reverse++result)) := by
  cases carry <;>
    apply congrArg some <;> apply congrArg (Config.mk _) <;>
      funext r <;> fin_cases r <;> simp [addBits, addConfig] <;> rfl

/-- Actual stack instructions for the full carry loop, with an explicit
linear instruction bound and no assumed arithmetic primitive. -/
theorem add_loop (carry : Bool) (first second result : List Bool)
    (base : Register additionProgram → List Bool) :
    ∃ steps ≤ 3*(first.length+second.length)+3,
      Machine.run (step additionProgram) steps
        (addConfig (carryControl carry) base first second result) =
        some (addConfig 34 base [] [] ((addBits carry first second).reverse++result)) := by
  induction first generalizing carry second result with
  | nil =>
      induction second generalizing carry result with
      | nil =>
          refine ⟨if carry then 3 else 2, ?_, add_empty carry result base⟩
          cases carry <;> simp
      | cons b second ih =>
          obtain ⟨steps, bound, executed⟩ := ih (carryBit carry false b) (sumBit carry false b::result)
          refine ⟨3+steps, by simp only [List.length_cons, List.length_nil] at *; omega, ?_⟩
          rw [Machine.run_add, add_right, Option.bind_some, executed]
          simp only [addBits, List.reverse_cons, List.append_assoc, List.singleton_append]
  | cons a first ih =>
      cases second with
      | nil =>
          obtain ⟨steps, bound, executed⟩ := ih (carryBit carry a false) [] (sumBit carry a false::result)
          refine ⟨3+steps, by simp only [List.length_cons, List.length_nil] at *; omega, ?_⟩
          rw [Machine.run_add, add_left, Option.bind_some, executed]
          simp only [addBits, List.reverse_cons, List.append_assoc, List.singleton_append]
      | cons b second =>
          obtain ⟨steps, bound, executed⟩ := ih (carryBit carry a b) second (sumBit carry a b::result)
          refine ⟨3+steps, by simp only [List.length_cons] at *; omega, ?_⟩
          rw [Machine.run_add, add_pair, Option.bind_some, executed]
          simp only [addBits, List.reverse_cons, List.append_assoc, List.singleton_append]

end Counting.StackMachine.Arithmetic
