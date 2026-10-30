import Counting.StackEncodingFlaggedCorrectness
import Counting.StackRoutineBoundedLoop

/-! Sequential access to binary-framed fields without expanding their values. -/
namespace Counting.StackMachine.FieldAccess

/-- Skip a single frame, consuming a malformed suffix entirely. -/
def skipRest : List Bool → List Bool
  | false::rest => rest
  | true::_::rest => skipRest rest
  | _ => []

def skipCost : List Bool → Nat
  | false::_ => 1
  | true::_::rest => 2+skipCost rest
  | [true] => 2
  | [] => 1

theorem skipRest_frame (payload suffix : List Bool) :
    skipRest (Encoding.frame payload++suffix)=suffix := by
  induction payload with
  | nil => rfl
  | cons bit rest ih => simpa only [Encoding.frame,List.cons_append,skipRest] using ih

theorem skipCost_frame (payload suffix : List Bool) :
    skipCost (Encoding.frame payload++suffix)=2*payload.length+1 := by
  induction payload with
  | nil => rfl
  | cons bit rest ih =>
      simp only [Encoding.frame,List.cons_append,skipCost,ih,List.length_cons]
      omega

theorem skipRest_length (input : List Bool) : (skipRest input).length ≤ input.length := by
  induction input using skipRest.induct with
  | case1 rest => simp [skipRest]
  | case2 bit rest ih => simp only [skipRest,List.length_cons]; omega
  | case3 input first second => simp [skipRest.eq_3 input first second]

theorem skipCost_le (input : List Bool) : skipCost input ≤ input.length+1 := by
  induction input using skipCost.induct with
  | case1 rest => simp [skipCost]
  | case2 bit rest ih => simp only [skipCost,List.length_cons]; omega
  | case3 => simp [skipCost]
  | case4 => simp [skipCost]

/-- The suffix pays for future iterations, yielding a linear total scan
bound even when the requested index exceeds the number of fields. -/
theorem skipCost_amortized (input : List Bool) :
    skipCost input+(skipRest input).length ≤ input.length+1 := by
  induction input using skipCost.induct with
  | case1 rest => simp only [skipCost,skipRest,List.length_cons]; omega
  | case2 bit rest ih => simp only [skipCost,skipRest,List.length_cons]; omega
  | case3 => simp [skipCost,skipRest]
  | case4 => simp [skipCost,skipRest]

/-- No arithmetic on the encoded field value occurs: each payload bit
requires its delimiter pop and its data pop. -/
def skipProgram (extra : Nat) (source : Fin (extra+2)) : Program where
  extraRegisters := extra
  states := 2
  code control := match control.val with
    | 0 => .pop source 2 2 1
    | 1 => .pop source 2 0 0
    | _ => .halt

def skipConfig (extra : Nat) (source : Fin (extra+2))
    (control : Control (skipProgram extra source))
    (base : Fin (extra+2) → List Bool) (input : List Bool) : Config (skipProgram extra source) :=
  ⟨control,fun r => if r=source then input else base r⟩

theorem skip_pair (extra : Nat) (source : Fin (extra+2))
    (base : Fin (extra+2) → List Bool) (bit : Bool) (rest : List Bool) :
    Machine.run (step (skipProgram extra source)) 2 (skipConfig extra source 0 base (true::bit::rest))=
      some (skipConfig extra source 0 base rest) := by
  cases bit <;> simp [Machine.run,step,skipProgram,skipConfig]
  all_goals
    refine ⟨rfl,?_⟩
    funext r
    by_cases h : r=source <;> simp [h]

theorem skip_run (extra : Nat) (source : Fin (extra+2))
    (base : Fin (extra+2) → List Bool) (input : List Bool) :
    Machine.run (step (skipProgram extra source)) (skipCost input) (skipConfig extra source 0 base input)=
      some (skipConfig extra source 2 base (skipRest input)) := by
  induction input using skipCost.induct with
  | case1 rest =>
      simp [skipCost,skipRest,Machine.run,step,skipProgram,skipConfig]
      refine ⟨rfl,?_⟩
      funext r
      by_cases h : r=source <;> simp [h]
  | case2 bit rest ih => rw [skipCost,Machine.run_add,skip_pair,Option.bind_some,ih]; rfl
  | case3 =>
      simp [skipCost,skipRest,Machine.run,step,skipProgram,skipConfig]
      refine ⟨rfl,?_⟩
      funext r
      by_cases h : r=source <;> simp [h]
  | case4 => simp [skipCost,skipRest,Machine.run,step,skipProgram,skipConfig]; exact ⟨rfl,rfl⟩

theorem skip_executes (extra : Nat) (source : Fin (extra+2)) (store : Fin (extra+2) → List Bool) :
    Routine.Executes (Routine.ofProgram (skipProgram extra source)) store (skipCost (store source))
      (Function.update store source (skipRest (store source))) := by
  have start : skipConfig extra source 0 store (store source)=(⟨0,store⟩:Config (skipProgram extra source)) := by
    apply congrArg (Config.mk _)
    funext r
    by_cases h : r=source <;> simp_all
  refine ⟨skipConfig extra source 2 store (skipRest (store source)),?_,rfl,?_⟩
  · rw [←start]
    exact skip_run extra source store (store source)
  · funext r
    by_cases h : r=source
    · subst r; simp [skipConfig]
    · simp [skipConfig,h]

end Counting.StackMachine.FieldAccess
