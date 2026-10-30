import Counting.StackFrameSeek

/-! Move framed prefixes without decoding or expanding their numeric values. -/
namespace Counting.StackMachine.FieldAccess

def frameFront : List Bool → List Bool
  | false::_ => [false]
  | true::bit::rest => true::bit::frameFront rest
  | [true] => [true]
  | [] => []

def moveCost : List Bool → Nat
  | false::_ => 2
  | true::_::rest => 4+moveCost rest
  | [true] => 3
  | [] => 1

theorem frameFront_append (input : List Bool) : frameFront input++skipRest input=input := by
  induction input using moveCost.induct with
  | case1 rest => rfl
  | case2 bit rest ih => simpa only [frameFront,skipRest,List.cons_append] using congrArg (fun xs=>true::bit::xs) ih
  | case3 => rfl
  | case4 => rfl

theorem frameFront_frame (payload suffix : List Bool) :
    frameFront (Encoding.frame payload++suffix)=Encoding.frame payload := by
  have split := frameFront_append (Encoding.frame payload++suffix)
  rw [skipRest_frame] at split
  exact List.append_cancel_right split

theorem moveCost_amortized (input : List Bool) :
    moveCost input+2*(skipRest input).length≤2*input.length+1 := by
  induction input using moveCost.induct with
  | case1 rest => simp only [moveCost,skipRest,List.length_cons]; omega
  | case2 bit rest ih => simp only [moveCost,skipRest,List.length_cons]; omega
  | case3 => simp [moveCost,skipRest]
  | case4 => simp [moveCost,skipRest]

def moveProgram (extra : Nat) (source target : Fin (extra+2)) : Program where
  extraRegisters := extra
  states := 6
  code control := match control.val with
    | 0 => .pop source 6 1 2
    | 1 => .push target false 6
    | 2 => .push target true 3
    | 3 => .pop source 6 4 5
    | 4 => .push target false 0
    | 5 => .push target true 0
    | _ => .halt

def moveConfig (extra : Nat) (source target : Fin (extra+2))
    (control : Control (moveProgram extra source target))
    (base : Fin (extra+2) → List Bool) (input output : List Bool) : Config (moveProgram extra source target) :=
  ⟨control,fun r => if r=source then input else if r=target then output else base r⟩

theorem move_pair (extra : Nat) (source target : Fin (extra+2)) (distinct : source≠target)
    (base : Fin (extra+2) → List Bool) (bit : Bool) (input output : List Bool) :
    Machine.run (step (moveProgram extra source target)) 4
      (moveConfig extra source target 0 base (true::bit::input) output)=
      some (moveConfig extra source target 0 base input (bit::true::output)) := by
  cases bit <;> simp [Machine.run,step,moveProgram,moveConfig,distinct,Ne.symm distinct]
  all_goals
    refine ⟨rfl,?_⟩
    funext r
    by_cases a : r=source
    · subst r; simp [distinct]
    · by_cases b : r=target
      · subst r; simp [Ne.symm distinct]
      · simp [a,b]

theorem move_run (extra : Nat) (source target : Fin (extra+2)) (distinct : source≠target)
    (base : Fin (extra+2) → List Bool) (input output : List Bool) :
    Machine.run (step (moveProgram extra source target)) (moveCost input)
      (moveConfig extra source target 0 base input output)=
      some (moveConfig extra source target 6 base (skipRest input) ((frameFront input).reverse++output)) := by
  induction input using moveCost.induct generalizing output with
  | case1 rest =>
      simp [moveCost,frameFront,skipRest,Machine.run,step,moveProgram,moveConfig,Ne.symm distinct]
      refine ⟨rfl,?_⟩
      funext r
      by_cases a : r=source
      · subst r; simp [distinct]
      · by_cases b : r=target
        · subst r; simp [Ne.symm distinct]
        · simp [a,b]
  | case2 bit input ih =>
      rw [moveCost,Machine.run_add,move_pair extra source target distinct,Option.bind_some,ih]
      simp only [skipRest,frameFront,List.reverse_cons,List.append_assoc,List.cons_append,List.nil_append]
  | case3 =>
      simp [moveCost,frameFront,skipRest,Machine.run,step,moveProgram,moveConfig,distinct,Ne.symm distinct]
      refine ⟨rfl,?_⟩
      funext r
      by_cases a : r=source
      · subst r; simp [distinct]
      · by_cases b : r=target
        · subst r; simp [Ne.symm distinct]
        · simp [a,b]
  | case4 => simp [moveCost,frameFront,skipRest,Machine.run,step,moveProgram,moveConfig]; exact ⟨rfl,rfl⟩

theorem move_executes (extra : Nat) (source target : Fin (extra+2)) (distinct : source≠target)
    (store : Fin (extra+2) → List Bool) :
    Routine.Executes (Routine.ofProgram (moveProgram extra source target)) store (moveCost (store source))
      (Function.update (Function.update store source (skipRest (store source))) target
        ((frameFront (store source)).reverse++store target)) := by
  have start : moveConfig extra source target 0 store (store source) (store target)=
      (⟨0,store⟩:Config (moveProgram extra source target)) := by
    apply congrArg (Config.mk _)
    funext r
    split_ifs <;> simp_all
  refine ⟨moveConfig extra source target 6 store (skipRest (store source))
    ((frameFront (store source)).reverse++store target),?_,rfl,?_⟩
  · rw [←start]
    exact move_run extra source target distinct store (store source) (store target)
  · funext r
    dsimp only [moveConfig]
    split_ifs <;> simp_all [Function.update]
    intro eq
    exact (distinct eq).elim

end Counting.StackMachine.FieldAccess
