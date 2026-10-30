import Counting.StackComposition

/-! A finite-control loop consuming one counter bit per iteration. The body
is an actual routine; a caller supplies its proved execution, not an oracle.
Each iteration pays one pop and one jump in addition to the body steps. -/
namespace Counting.StackMachine.Routine

abbrev Store (registers : Nat) := Fin (registers+2) → List Bool

def loopControl {registers : Nat} (body : Routine registers) (control : Control body.program) :
    Fin (body.states+3) := ⟨control.val+2,by have bounded := control.isLt; change control.val < body.states+1 at bounded; omega⟩

def forEach {registers : Nat} (counter : Fin (registers+2)) (body : Routine registers) : Routine registers where
  states := body.states+2
  code control :=
    if control.val = 0 then .pop counter 1 (loopControl body 0) (loopControl body 0)
    else if control.val = 1 then .halt
    else match body.code ⟨control.val-2,by have := control.isLt; omega⟩ with
      | .halt => .jump 0
      | instruction => instruction.relabel (loopControl body)

def loopConfig {registers : Nat} (counter : Fin (registers+2)) (body : Routine registers)
    (config : Config body.program) : Config (forEach counter body).program :=
  ⟨loopControl body config.control,config.store⟩

theorem repeat_body_code {registers : Nat} (counter : Fin (registers+2)) (body : Routine registers)
    (control : Control body.program) :
    (forEach counter body).code (loopControl body control) =
      match body.code control with
      | .halt => .jump 0
      | instruction => instruction.relabel (loopControl body) := by
  have notZero : ¬control.val+2 = 0 := by omega
  have notOne : ¬control.val+2 = 1 := by omega
  simp only [forEach,loopControl,notZero,notOne,if_false,Nat.add_sub_cancel]
  rfl

theorem loop_step {registers : Nat} (counter : Fin (registers+2)) (body : Routine registers)
    (config next : Config body.program) (success : step body.program config = some next) :
    step (forEach counter body).program (loopConfig counter body config) = some (loopConfig counter body next) := by
  unfold step at success ⊢
  dsimp only [loopConfig,program] at success ⊢
  rw [repeat_body_code]
  cases instruction : body.code config.control with
  | halt => simp [instruction] at success
  | jump target =>
      simp only [instruction,Option.some.injEq] at success
      subst next
      rfl
  | push register bit target =>
      simp only [instruction,Option.some.injEq] at success
      subst next
      rfl
  | pop register empty zero one =>
      cases contents : config.store register with
      | nil =>
          simp only [instruction,contents,Option.some.injEq] at success
          subst next
          simp only [Instruction.relabel,contents]
      | cons bit rest =>
          simp only [instruction,contents,Option.some.injEq] at success
          subst next
          cases bit <;> simp only [Instruction.relabel,contents,ite_true,Bool.false_eq_true,if_false]

theorem loop_halt {registers : Nat} (counter : Fin (registers+2)) (body : Routine registers)
    (config : Config body.program) (halted : step body.program config = none) :
    step (forEach counter body).program (loopConfig counter body config) =
      some ⟨0,config.store⟩ := by
  have stop : body.code config.control = .halt := by
    cases instruction : body.code config.control <;> simp_all [step,program]
    split at halted <;> contradiction
  unfold step
  dsimp only [loopConfig,program]
  rw [repeat_body_code,stop]

theorem loop_run {registers : Nat} (counter : Fin (registers+2)) (body : Routine registers) (steps : Nat)
    {start finish : Config body.program} (success : Machine.run (step body.program) steps start = some finish) :
    Machine.run (step (forEach counter body).program) steps (loopConfig counter body start) =
      some (loopConfig counter body finish) := by
  induction steps generalizing start with
  | zero => have equal := Option.some.inj success; subst finish; rfl
  | succ steps ih =>
      cases next : step body.program start with
      | none => simp only [Machine.run,next,Option.bind_none] at success; contradiction
      | some middle =>
          have tail : Machine.run (step body.program) steps middle = some finish := by
            simpa only [Machine.run,next,Option.bind_some] using success
          rw [Machine.run,loop_step counter body start middle next,Option.bind_some]
          exact ih tail

theorem repeat_empty {registers : Nat} (counter : Fin (registers+2)) (body : Routine registers)
    (store : Store registers) (empty : store counter = []) :
    Machine.run (step (forEach counter body).program) 1 ⟨0,store⟩ = some ⟨1,store⟩ ∧
      step (forEach counter body).program ⟨1,store⟩ = none := by
  constructor
  · simp [Machine.run,step,program,forEach,empty]
    rfl
  · simp [step,program,forEach]

theorem repeat_iteration {registers : Nat} (counter : Fin (registers+2)) (body : Routine registers)
    (store : Store registers) (bit : Bool) (rest : List Bool) (contents : store counter = bit::rest)
    (steps : Nat) (finish : Config body.program)
    (executed : Machine.run (step body.program) steps ⟨0,Function.update store counter rest⟩ = some finish)
    (halted : step body.program finish = none) :
    Machine.run (step (forEach counter body).program) (steps+2) ⟨0,store⟩ = some ⟨0,finish.store⟩ := by
  have first : step (forEach counter body).program (⟨0,store⟩ : Config (forEach counter body).program) =
      some (loopConfig counter body ⟨0,Function.update store counter rest⟩) := by
    simp [step,program,forEach,contents,loopConfig]
  rw [show steps+2 = (steps+1)+1 by omega,Machine.run,first,Option.bind_some,
    Machine.run_add,loop_run counter body steps executed,Option.bind_some]
  rw [Machine.run,loop_halt counter body finish halted,Option.bind_some]
  rfl

end Counting.StackMachine.Routine
