import Counting.StackLoop

namespace Counting.StackMachine.Routine

/-- Consume one bit per iteration and enter the appropriate finite control
state of one common body. Neither the number nor the value of the input bits
is known to the compiled machine in advance. -/
def forBits {registers : Nat} (counter : Fin (registers+2)) (body : Routine registers)
    (zero one : Control body.program) : Routine registers where
  states := body.states+2
  code control :=
    if control.val = 0 then .pop counter 1 (loopControl body zero) (loopControl body one)
    else if control.val = 1 then .halt
    else match body.code ⟨control.val-2,by have := control.isLt; omega⟩ with
      | .halt => .jump 0
      | instruction => instruction.relabel (loopControl body)

def bitsConfig {registers : Nat} (counter : Fin (registers+2)) (body : Routine registers)
    (zero one : Control body.program) (config : Config body.program) : Config (forBits counter body zero one).program :=
  ⟨loopControl body config.control,config.store⟩

theorem bits_body_code {registers : Nat} (counter : Fin (registers+2)) (body : Routine registers)
    (zero one : Control body.program) (control : Control body.program) :
    (forBits counter body zero one).code (loopControl body control) =
      match body.code control with
      | .halt => .jump 0
      | instruction => instruction.relabel (loopControl body) := by
  have notZero : ¬control.val+2 = 0 := by omega
  have notOne : ¬control.val+2 = 1 := by omega
  simp only [forBits,loopControl,notZero,notOne,if_false,Nat.add_sub_cancel]
  rfl

theorem bits_step {registers : Nat} (counter : Fin (registers+2)) (body : Routine registers)
    (zero one : Control body.program) (config next : Config body.program)
    (success : step body.program config = some next) :
    step (forBits counter body zero one).program (bitsConfig counter body zero one config) =
      some (bitsConfig counter body zero one next) := by
  unfold step at success ⊢
  dsimp only [bitsConfig,program] at success ⊢
  rw [bits_body_code]
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
  | pop register empty falseTarget trueTarget =>
      cases contents : config.store register with
      | nil =>
          simp only [instruction,contents,Option.some.injEq] at success
          subst next
          simp only [Instruction.relabel,contents]
      | cons bit rest =>
          simp only [instruction,contents,Option.some.injEq] at success
          subst next
          cases bit <;> simp only [Instruction.relabel,contents,ite_true,Bool.false_eq_true,if_false]

theorem bits_halt {registers : Nat} (counter : Fin (registers+2)) (body : Routine registers)
    (zero one : Control body.program) (config : Config body.program) (halted : step body.program config = none) :
    step (forBits counter body zero one).program (bitsConfig counter body zero one config) =
      some ⟨0,config.store⟩ := by
  have stop : body.code config.control = .halt := by
    cases instruction : body.code config.control <;> simp_all [step,program]
    split at halted <;> contradiction
  unfold step
  dsimp only [bitsConfig,program]
  rw [bits_body_code,stop]

theorem bits_run {registers : Nat} (counter : Fin (registers+2)) (body : Routine registers)
    (zero one : Control body.program) (steps : Nat)
    {start finish : Config body.program} (success : Machine.run (step body.program) steps start = some finish) :
    Machine.run (step (forBits counter body zero one).program) steps (bitsConfig counter body zero one start) =
      some (bitsConfig counter body zero one finish) := by
  induction steps generalizing start with
  | zero => have equal := Option.some.inj success; subst finish; rfl
  | succ steps ih =>
      cases next : step body.program start with
      | none => simp only [Machine.run,next,Option.bind_none] at success; contradiction
      | some middle =>
          have tail : Machine.run (step body.program) steps middle = some finish := by
            simpa only [Machine.run,next,Option.bind_some] using success
          rw [Machine.run,bits_step counter body zero one start middle next,Option.bind_some]
          exact ih tail

theorem bits_empty {registers : Nat} (counter : Fin (registers+2)) (body : Routine registers)
    (zero one : Control body.program) (store : Store registers) (empty : store counter = []) :
    Machine.run (step (forBits counter body zero one).program) 1 ⟨0,store⟩ = some ⟨1,store⟩ ∧
      step (forBits counter body zero one).program ⟨1,store⟩ = none := by
  constructor
  · simp [Machine.run,step,program,forBits,empty]
    rfl
  · simp [step,program,forBits]

theorem bits_iteration {registers : Nat} (counter : Fin (registers+2)) (body : Routine registers)
    (zero one : Control body.program) (store : Store registers) (bit : Bool) (rest : List Bool)
    (contents : store counter = bit::rest) (steps : Nat) (finish : Config body.program)
    (executed : Machine.run (step body.program) steps
      ⟨if bit then one else zero,Function.update store counter rest⟩ = some finish)
    (halted : step body.program finish = none) :
    Machine.run (step (forBits counter body zero one).program) (steps+2) ⟨0,store⟩ = some ⟨0,finish.store⟩ := by
  have first : step (forBits counter body zero one).program
      (⟨0,store⟩ : Config (forBits counter body zero one).program) =
      some (bitsConfig counter body zero one ⟨if bit then one else zero,Function.update store counter rest⟩) := by
    cases bit <;> simp [step,program,forBits,contents,bitsConfig]
  rw [show steps+2 = (steps+1)+1 by omega,Machine.run,first,Option.bind_some,
    Machine.run_add,bits_run counter body zero one steps executed,Option.bind_some]
  rw [Machine.run,bits_halt counter body zero one finish halted,Option.bind_some]
  rfl

end Counting.StackMachine.Routine
