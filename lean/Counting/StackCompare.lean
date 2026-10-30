import Counting.StackRoutineLists
import Counting.StackCompilerComplete

/-! Finite-control equality of bit strings. Both operands are consumed,
including on a mismatch; the Boolean result is prepended to the output
register and all unrelated registers are preserved. -/
namespace Counting.StackMachine.Compare

def equalityProgram (extra : Nat) (left right output : Fin (extra+2)) : Program where
  extraRegisters := extra
  states := 8
  code control := match control.val with
    | 0 => .pop left 1 2 3
    | 1 => .pop right 4 5 5
    | 2 => .pop right 5 0 5
    | 3 => .pop right 5 5 0
    | 4 => .push output true 8
    | 5 => .pop left 6 5 5
    | 6 => .pop right 7 6 6
    | 7 => .push output false 8
    | _ => .halt

def config (extra : Nat) (left right output : Fin (extra+2))
    (control : Control (equalityProgram extra left right output))
    (base : Fin (extra+2) → List Bool) (a b result : List Bool) :
    Config (equalityProgram extra left right output) :=
  ⟨control, fun r => if r=left then a else if r=right then b else if r=output then result else base r⟩

theorem clear_left_step (extra : Nat) (left right output : Fin (extra+2))
    (base : Fin (extra+2) → List Bool) (bit : Bool) (a b result : List Bool) :
    step (equalityProgram extra left right output) (config extra left right output 5 base (bit::a) b result) =
      some (config extra left right output 5 base a b result) := by
  cases bit <;> simp [step,equalityProgram,config]
  all_goals
    refine ⟨rfl, ?_⟩
    funext r
    by_cases same : r=left
    · subst r; simp
    · simp [same]

theorem clear_left_run (extra : Nat) (left right output : Fin (extra+2))
    (base : Fin (extra+2) → List Bool) (a b result : List Bool) :
    Machine.run (step (equalityProgram extra left right output)) (a.length+1)
      (config extra left right output 5 base a b result) =
      some (config extra left right output 6 base [] b result) := by
  induction a with
  | nil => simp [Machine.run,step,equalityProgram,config]; rfl
  | cons bit a ih =>
      rw [List.length_cons,Machine.run,clear_left_step extra left right output,
        Option.bind_some,ih]

theorem clear_right_step (extra : Nat) (left right output : Fin (extra+2))
    (lr : left ≠ right)
    (base : Fin (extra+2) → List Bool) (bit : Bool) (b result : List Bool) :
    step (equalityProgram extra left right output) (config extra left right output 6 base [] (bit::b) result) =
      some (config extra left right output 6 base [] b result) := by
  cases bit <;> simp [step,equalityProgram,config,Ne.symm lr]
  all_goals
    refine ⟨rfl, ?_⟩
    funext r
    by_cases first : r=left
    · subst r; simp [lr]
    · by_cases second : r=right
      · subst r; simp [Ne.symm lr]
      · simp [first,second]

theorem clear_right_run (extra : Nat) (left right output : Fin (extra+2))
    (lr : left ≠ right)
    (base : Fin (extra+2) → List Bool) (b result : List Bool) :
    Machine.run (step (equalityProgram extra left right output)) (b.length+1)
      (config extra left right output 6 base [] b result) =
      some (config extra left right output 7 base [] [] result) := by
  induction b with
  | nil => simp [Machine.run,step,equalityProgram,config,Ne.symm lr]; rfl
  | cons bit b ih =>
      rw [List.length_cons,Machine.run,clear_right_step extra left right output lr,
        Option.bind_some,ih]

theorem write_result (extra : Nat) (left right output : Fin (extra+2))
    (lo : left ≠ output) (ro : right ≠ output)
    (base : Fin (extra+2) → List Bool) (result : List Bool) (answer : Bool) :
    step (equalityProgram extra left right output)
      (config extra left right output (if answer then 4 else 7) base [] [] result) =
      some (config extra left right output 8 base [] [] (answer::result)) := by
  cases answer <;> simp [step,equalityProgram,config,Ne.symm lo,Ne.symm ro]
  all_goals
    refine ⟨rfl, ?_⟩
    funext r
    by_cases first : r=left
    · subst r; simp [lo]
    · by_cases second : r=right
      · subst r; simp [ro]
      · by_cases third : r=output
        · subst r; simp [Ne.symm lo,Ne.symm ro]
        · simp [first,second,third]

theorem failure_run (extra : Nat) (left right output : Fin (extra+2))
    (lr : left ≠ right) (lo : left ≠ output) (ro : right ≠ output)
    (base : Fin (extra+2) → List Bool) (a b result : List Bool) :
    Machine.run (step (equalityProgram extra left right output)) (a.length+b.length+3)
      (config extra left right output 5 base a b result) =
      some (config extra left right output 8 base [] [] (false::result)) := by
  have emitted := write_result extra left right output lo ro base result false
  simp only [Bool.false_eq_true,if_false] at emitted
  rw [show a.length+b.length+3=(a.length+1)+((b.length+1)+1) by omega,
    Machine.run_add,clear_left_run extra left right output,Option.bind_some,
    Machine.run_add,clear_right_run extra left right output lr,Option.bind_some,
    Machine.run,emitted,Option.bind_some]
  rfl

theorem same_head (extra : Nat) (left right output : Fin (extra+2))
    (lr : left ≠ right) (base : Fin (extra+2) → List Bool) (bit : Bool)
    (a b result : List Bool) :
    Machine.run (step (equalityProgram extra left right output)) 2
      (config extra left right output 0 base (bit::a) (bit::b) result) =
      some (config extra left right output 0 base a b result) := by
  cases bit <;> simp [Machine.run,step,equalityProgram,config,Ne.symm lr]
  all_goals
    refine ⟨rfl, ?_⟩
    funext r
    by_cases first : r=left
    · subst r; simp [lr]
    · by_cases second : r=right
      · subst r; simp [Ne.symm lr]
      · simp [first,second]

theorem different_head (extra : Nat) (left right output : Fin (extra+2))
    (lr : left ≠ right) (base : Fin (extra+2) → List Bool) (first second : Bool)
    (different : first ≠ second) (a b result : List Bool) :
    Machine.run (step (equalityProgram extra left right output)) 2
      (config extra left right output 0 base (first::a) (second::b) result) =
      some (config extra left right output 5 base a b result) := by
  cases first <;> cases second <;> simp_all [Machine.run,step,equalityProgram,config,Ne.symm lr]
  all_goals
    refine ⟨rfl, ?_⟩
    funext r
    by_cases a : r=left
    · subst r; simp [lr]
    · by_cases b : r=right
      · subst r; simp [Ne.symm lr]
      · simp [a,b]

theorem left_empty (extra : Nat) (left right output : Fin (extra+2))
    (lr : left ≠ right) (base : Fin (extra+2) → List Bool) (bit : Bool) (b result : List Bool) :
    Machine.run (step (equalityProgram extra left right output)) 2
      (config extra left right output 0 base [] (bit::b) result) =
      some (config extra left right output 5 base [] b result) := by
  cases bit <;> simp [Machine.run,step,equalityProgram,config,Ne.symm lr]
  all_goals
    refine ⟨rfl, ?_⟩
    funext r
    by_cases first : r=left
    · subst r; simp [lr]
    · by_cases second : r=right
      · subst r; simp [Ne.symm lr]
      · simp [first,second]

theorem right_empty (extra : Nat) (left right output : Fin (extra+2))
    (lr : left ≠ right) (base : Fin (extra+2) → List Bool) (bit : Bool) (a result : List Bool) :
    Machine.run (step (equalityProgram extra left right output)) 2
      (config extra left right output 0 base (bit::a) [] result) =
      some (config extra left right output 5 base a [] result) := by
  cases bit <;> simp [Machine.run,step,equalityProgram,config,Ne.symm lr]
  all_goals
    refine ⟨rfl, ?_⟩
    funext r
    by_cases first : r=left
    · subst r; simp
    · simp [first]

theorem both_empty (extra : Nat) (left right output : Fin (extra+2))
    (lr : left ≠ right) (lo : left ≠ output) (ro : right ≠ output)
    (base : Fin (extra+2) → List Bool) (result : List Bool) :
    Machine.run (step (equalityProgram extra left right output)) 3
      (config extra left right output 0 base [] [] result) =
      some (config extra left right output 8 base [] [] (true::result)) := by
  have firstTwo : Machine.run (step (equalityProgram extra left right output)) 2
      (config extra left right output 0 base [] [] result) =
      some (config extra left right output 4 base [] [] result) := by
    simp [Machine.run,step,equalityProgram,config,Ne.symm lr]
    rfl
  have emitted := write_result extra left right output lo ro base result true
  simp only [if_true] at emitted
  rw [show 3=2+1 by rfl,Machine.run_add,firstTwo,Option.bind_some,Machine.run,
    emitted,Option.bind_some]
  rfl

/-- Exact cost of the finite-state routine, including draining both operands. -/
def equalityCost : List Bool → List Bool → Nat
  | [], [] => 3
  | [], _::b => 2+(b.length+3)
  | _::a, [] => 2+(a.length+3)
  | bit::a, other::b => if bit=other then 2+equalityCost a b else 2+(a.length+b.length+3)

theorem equalityCost_le (a b : List Bool) : equalityCost a b ≤ a.length+b.length+5 := by
  induction a generalizing b with
  | nil => cases b <;> simp [equalityCost]; omega
  | cons bit a ih =>
      cases b with
      | nil => simp [equalityCost]; omega
      | cons other b =>
          have tailBound := ih b
          simp only [equalityCost,List.length_cons]
          split_ifs <;> omega

theorem equality_exact_run (extra : Nat) (left right output : Fin (extra+2))
    (lr : left ≠ right) (lo : left ≠ output) (ro : right ≠ output)
    (base : Fin (extra+2) → List Bool) (a b result : List Bool) :
    Machine.run (step (equalityProgram extra left right output)) (equalityCost a b)
      (config extra left right output 0 base a b result) =
      some (config extra left right output 8 base [] [] (decide (a=b)::result)) := by
  induction a generalizing b with
  | nil =>
      cases b with
      | nil => exact both_empty extra left right output lr lo ro base result
      | cons bit b =>
          rw [equalityCost,Machine.run_add,left_empty extra left right output lr,Option.bind_some]
          simpa using failure_run extra left right output lr lo ro base [] b result
  | cons bit a ih =>
      cases b with
      | nil =>
          rw [equalityCost,Machine.run_add,right_empty extra left right output lr,Option.bind_some]
          simpa using failure_run extra left right output lr lo ro base a [] result
      | cons other b =>
          by_cases equal : bit=other
          · subst other
            rw [equalityCost,if_pos rfl,Machine.run_add,same_head extra left right output lr,
              Option.bind_some,ih]
            simp only [List.cons.injEq,true_and]
          · rw [equalityCost,if_neg equal,Machine.run_add,
              different_head extra left right output lr base bit other equal,
              Option.bind_some,failure_run extra left right output lr lo ro]
            simp only [List.cons.injEq,equal,false_and,decide_false]

theorem equality_run (extra : Nat) (left right output : Fin (extra+2))
    (lr : left ≠ right) (lo : left ≠ output) (ro : right ≠ output)
    (base : Fin (extra+2) → List Bool) (a b result : List Bool) :
    ∃ steps ≤ a.length+b.length+5,
      Machine.run (step (equalityProgram extra left right output)) steps
        (config extra left right output 0 base a b result) =
        some (config extra left right output 8 base [] [] (decide (a=b)::result)) :=
  ⟨equalityCost a b,equalityCost_le a b,equality_exact_run extra left right output lr lo ro base a b result⟩

theorem equality_halted (extra : Nat) (left right output : Fin (extra+2))
    (base : Fin (extra+2) → List Bool) (a b result : List Bool) :
    step (equalityProgram extra left right output) (config extra left right output 8 base a b result) = none := rfl

/-- Store-level contract, suitable for sequential composition and bounded loops. -/
theorem equality_executes (extra : Nat) (left right output : Fin (extra+2))
    (lr : left ≠ right) (lo : left ≠ output) (ro : right ≠ output)
    (store : Fin (extra+2) → List Bool) :
    Routine.Executes (Routine.ofProgram (equalityProgram extra left right output)) store
      (equalityCost (store left) (store right))
      (Function.update (Function.update (Function.update store left []) right []) output
        (decide (store left=store right)::store output)) := by
  have start : config extra left right output 0 store (store left) (store right) (store output) =
      (⟨0,store⟩ : Config (equalityProgram extra left right output)) := by
    apply congrArg (Config.mk _)
    funext r
    split_ifs <;> simp_all
  refine ⟨config extra left right output 8 store [] [] (decide (store left=store right)::store output),
    ?_,equality_halted _ _ _ _ _ _ _ _,?_⟩
  · rw [← start]
    exact equality_exact_run extra left right output lr lo ro store (store left) (store right) (store output)
  · funext r
    dsimp only [config]
    split_ifs <;> simp_all [Function.update]
    · exact lo
    · exact ro

end Counting.StackMachine.Compare
