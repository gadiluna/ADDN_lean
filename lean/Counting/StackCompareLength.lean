import Counting.StackComparePreserving

/-! Length order, hence order of unary counters, with exact charged cost. -/
namespace Counting.StackMachine.Compare

def lengthLEProgram (extra : Nat) (left right output : Fin (extra+2)) : Program where
  extraRegisters := extra
  states := 8
  code control := match control.val with
    | 0 => .pop left 1 2 2
    | 1 => .pop right 4 1 1
    | 2 => .pop right 5 0 0
    | 4 => .push output true 8
    | 5 => .pop left 7 5 5
    | 7 => .push output false 8
    | _ => .halt

def lengthConfig (extra : Nat) (left right output : Fin (extra+2))
    (control : Control (lengthLEProgram extra left right output))
    (base : Fin (extra+2) → List Bool) (a b result : List Bool) :
    Config (lengthLEProgram extra left right output) :=
  ⟨control, fun r => if r=left then a else if r=right then b else if r=output then result else base r⟩

theorem length_drain_true_step (extra : Nat) (left right output : Fin (extra+2))
    (lr : left ≠ right) (base : Fin (extra+2) → List Bool) (bit : Bool) (b result : List Bool) :
    step (lengthLEProgram extra left right output) (lengthConfig extra left right output 1 base [] (bit::b) result) =
      some (lengthConfig extra left right output 1 base [] b result) := by
  cases bit <;> simp [step,lengthLEProgram,lengthConfig,Ne.symm lr]
  all_goals
    refine ⟨rfl,?_⟩
    funext r
    by_cases a : r=left
    · subst r; simp [lr]
    · by_cases c : r=right
      · subst r; simp [Ne.symm lr]
      · simp [a,c]

theorem length_drain_true (extra : Nat) (left right output : Fin (extra+2))
    (lr : left ≠ right) (base : Fin (extra+2) → List Bool) (b result : List Bool) :
    Machine.run (step (lengthLEProgram extra left right output)) (b.length+1)
      (lengthConfig extra left right output 1 base [] b result) =
      some (lengthConfig extra left right output 4 base [] [] result) := by
  induction b with
  | nil => simp [Machine.run,step,lengthLEProgram,lengthConfig,Ne.symm lr]; rfl
  | cons bit b ih =>
      rw [List.length_cons,Machine.run,length_drain_true_step extra left right output lr,
        Option.bind_some,ih]

theorem length_drain_false_step (extra : Nat) (left right output : Fin (extra+2))
    (base : Fin (extra+2) → List Bool) (bit : Bool) (a result : List Bool) :
    step (lengthLEProgram extra left right output) (lengthConfig extra left right output 5 base (bit::a) [] result) =
      some (lengthConfig extra left right output 5 base a [] result) := by
  cases bit <;> simp [step,lengthLEProgram,lengthConfig]
  all_goals
    refine ⟨rfl,?_⟩
    funext r
    by_cases same : r=left <;> simp [same]

theorem length_drain_false (extra : Nat) (left right output : Fin (extra+2))
    (base : Fin (extra+2) → List Bool) (a result : List Bool) :
    Machine.run (step (lengthLEProgram extra left right output)) (a.length+1)
      (lengthConfig extra left right output 5 base a [] result) =
      some (lengthConfig extra left right output 7 base [] [] result) := by
  induction a with
  | nil => simp [Machine.run,step,lengthLEProgram,lengthConfig]; rfl
  | cons bit a ih =>
      rw [List.length_cons,Machine.run,length_drain_false_step,Option.bind_some,ih]

theorem length_emit (extra : Nat) (left right output : Fin (extra+2))
    (lo : left ≠ output) (ro : right ≠ output)
    (base : Fin (extra+2) → List Bool) (result : List Bool) (answer : Bool) :
    step (lengthLEProgram extra left right output)
      (lengthConfig extra left right output (if answer then 4 else 7) base [] [] result) =
      some (lengthConfig extra left right output 8 base [] [] (answer::result)) := by
  cases answer <;> simp [step,lengthLEProgram,lengthConfig,Ne.symm lo,Ne.symm ro]
  all_goals
    refine ⟨rfl,?_⟩
    funext r
    by_cases a : r=left
    · subst r; simp [lo]
    · by_cases b : r=right
      · subst r; simp [ro]
      · by_cases c : r=output
        · subst r; simp [Ne.symm lo,Ne.symm ro]
        · simp [a,b,c]

theorem length_left_empty (extra : Nat) (left right output : Fin (extra+2))
    (lr : left ≠ right) (lo : left ≠ output) (ro : right ≠ output)
    (base : Fin (extra+2) → List Bool) (b result : List Bool) :
    Machine.run (step (lengthLEProgram extra left right output)) (b.length+3)
      (lengthConfig extra left right output 0 base [] b result) =
      some (lengthConfig extra left right output 8 base [] [] (true::result)) := by
  have first : step (lengthLEProgram extra left right output)
      (lengthConfig extra left right output 0 base [] b result) =
      some (lengthConfig extra left right output 1 base [] b result) := by
    simp [step,lengthLEProgram,lengthConfig]
    rfl
  have emitted := length_emit extra left right output lo ro base result true
  simp only [if_true] at emitted
  rw [show b.length+3=(b.length+2)+1 by omega,Machine.run,first,Option.bind_some,
    show b.length+2=(b.length+1)+1 by omega,Machine.run_add,length_drain_true extra left right output lr,
    Option.bind_some,Machine.run,emitted,Option.bind_some]
  rfl

theorem length_right_empty (extra : Nat) (left right output : Fin (extra+2))
    (lr : left ≠ right) (lo : left ≠ output) (ro : right ≠ output)
    (base : Fin (extra+2) → List Bool) (bit : Bool) (a result : List Bool) :
    Machine.run (step (lengthLEProgram extra left right output)) (a.length+4)
      (lengthConfig extra left right output 0 base (bit::a) [] result) =
      some (lengthConfig extra left right output 8 base [] [] (false::result)) := by
  have firstTwo : Machine.run (step (lengthLEProgram extra left right output)) 2
      (lengthConfig extra left right output 0 base (bit::a) [] result) =
      some (lengthConfig extra left right output 5 base a [] result) := by
    cases bit <;> simp [Machine.run,step,lengthLEProgram,lengthConfig,Ne.symm lr]
    all_goals
      refine ⟨rfl,?_⟩
      funext r
      by_cases same : r=left <;> simp [same]
  have emitted := length_emit extra left right output lo ro base result false
  simp only [Bool.false_eq_true,if_false] at emitted
  rw [show a.length+4=2+((a.length+1)+1) by omega,Machine.run_add,firstTwo,Option.bind_some,
    Machine.run_add,length_drain_false,Option.bind_some,Machine.run,emitted,Option.bind_some]
  rfl

theorem length_both_cons (extra : Nat) (left right output : Fin (extra+2))
    (lr : left ≠ right) (base : Fin (extra+2) → List Bool) (bit other : Bool) (a b result : List Bool) :
    Machine.run (step (lengthLEProgram extra left right output)) 2
      (lengthConfig extra left right output 0 base (bit::a) (other::b) result) =
      some (lengthConfig extra left right output 0 base a b result) := by
  cases bit <;> cases other <;> simp [Machine.run,step,lengthLEProgram,lengthConfig,Ne.symm lr]
  all_goals
    refine ⟨rfl,?_⟩
    funext r
    by_cases first : r=left
    · subst r; simp [lr]
    · by_cases second : r=right
      · subst r; simp [Ne.symm lr]
      · simp [first,second]

/-- Both lists are drained, so the transition count is independent of
which operand is shorter and of every payload bit. -/
theorem lengthLE_run (extra : Nat) (left right output : Fin (extra+2))
    (lr : left ≠ right) (lo : left ≠ output) (ro : right ≠ output)
    (base : Fin (extra+2) → List Bool) (a b result : List Bool) :
    Machine.run (step (lengthLEProgram extra left right output)) (a.length+b.length+3)
      (lengthConfig extra left right output 0 base a b result) =
      some (lengthConfig extra left right output 8 base [] [] (decide (a.length≤b.length)::result)) := by
  induction a generalizing b with
  | nil => simpa using length_left_empty extra left right output lr lo ro base b result
  | cons bit a ih =>
      cases b with
      | nil => simpa using length_right_empty extra left right output lr lo ro base bit a result
      | cons other b =>
          rw [show (bit::a).length+(other::b).length+3=2+(a.length+b.length+3) by simp; omega,
            Machine.run_add,length_both_cons extra left right output lr,Option.bind_some,ih]
          simp only [List.length_cons,Nat.add_le_add_iff_right]

theorem lengthLE_executes (extra : Nat) (left right output : Fin (extra+2))
    (lr : left ≠ right) (lo : left ≠ output) (ro : right ≠ output)
    (store : Fin (extra+2) → List Bool) :
    Routine.Executes (Routine.ofProgram (lengthLEProgram extra left right output)) store
      ((store left).length+(store right).length+3)
      (Function.update (Function.update (Function.update store left []) right []) output
        (decide ((store left).length≤(store right).length)::store output)) := by
  have start : lengthConfig extra left right output 0 store (store left) (store right) (store output) =
      (⟨0,store⟩ : Config (lengthLEProgram extra left right output)) := by
    apply congrArg (Config.mk _)
    funext r
    split_ifs <;> simp_all
  refine ⟨lengthConfig extra left right output 8 store [] []
    (decide ((store left).length≤(store right).length)::store output),?_,rfl,?_⟩
  · rw [← start]
    exact lengthLE_run extra left right output lr lo ro store (store left) (store right) (store output)
  · funext r
    dsimp only [lengthConfig]
    split_ifs <;> simp_all [Function.update]
    · exact lo
    · exact ro

end Counting.StackMachine.Compare
