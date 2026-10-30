import Counting.StackRoutineLists

/-! A charged unary-index drop, used by bit lookup and coordinate arithmetic. -/
namespace Counting.StackMachine.Lookup

def dropProgram (extra : Nat) (source counter : Fin (extra+2)) : Program where
  extraRegisters := extra
  states := 2
  code control := match control.val with
    | 0 => .pop counter 2 1 1
    | 1 => .pop source 0 0 0
    | _ => .halt

def dropConfig (extra : Nat) (source counter : Fin (extra+2))
    (control : Control (dropProgram extra source counter))
    (base : Fin (extra+2) → List Bool) (input count : List Bool) :
    Config (dropProgram extra source counter) :=
  ⟨control,fun r => if r=source then input else if r=counter then count else base r⟩

theorem drop_two (extra : Nat) (source counter : Fin (extra+2)) (distinct : source ≠ counter)
    (base : Fin (extra+2) → List Bool) (input count : List Bool) (token : Bool) :
    Machine.run (step (dropProgram extra source counter)) 2
      (dropConfig extra source counter 0 base input (token::count)) =
      some (dropConfig extra source counter 0 base input.tail count) := by
  cases token <;> cases input <;> simp [Machine.run,step,dropProgram,dropConfig,Ne.symm distinct,distinct]
  all_goals
    refine ⟨rfl,?_⟩
    funext r
    by_cases a : r=source
    · subst r; simp [distinct]
    · by_cases b : r=counter
      · subst r; simp [Ne.symm distinct]
      · simp [a,b]

/-- Counter bits need not be true: only their length determines the index.
Empty sources still pay every requested drop instruction. -/
theorem drop_run (extra : Nat) (source counter : Fin (extra+2)) (distinct : source ≠ counter)
    (base : Fin (extra+2) → List Bool) (input count : List Bool) :
    Machine.run (step (dropProgram extra source counter)) (2*count.length+1)
      (dropConfig extra source counter 0 base input count) =
      some (dropConfig extra source counter 2 base (input.drop count.length) []) := by
  induction count generalizing input with
  | nil => simp [Machine.run,step,dropProgram,dropConfig,Ne.symm distinct]; rfl
  | cons bit count ih =>
      rw [List.length_cons,show 2*(count.length+1)+1=2+(2*count.length+1) by omega,
        Machine.run_add,drop_two extra source counter distinct,Option.bind_some,ih]
      congr 2
      cases input <;> simp

theorem drop_executes (extra : Nat) (source counter : Fin (extra+2)) (distinct : source ≠ counter)
    (store : Fin (extra+2) → List Bool) :
    Routine.Executes (Routine.ofProgram (dropProgram extra source counter)) store
      (2*(store counter).length+1)
      (Function.update (Function.update store counter []) source ((store source).drop (store counter).length)) := by
  have start : dropConfig extra source counter 0 store (store source) (store counter) =
      (⟨0,store⟩ : Config (dropProgram extra source counter)) := by
    apply congrArg (Config.mk _)
    funext r
    split_ifs <;> simp_all
  refine ⟨dropConfig extra source counter 2 store ((store source).drop (store counter).length) [],?_,rfl,?_⟩
  · rw [←start]
    exact drop_run extra source counter distinct store (store source) (store counter)
  · funext r
    dsimp only [dropConfig]
    split_ifs <;> simp_all [Function.update]

end Counting.StackMachine.Lookup
