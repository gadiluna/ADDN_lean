import Counting.StackMachine

/-! Executable composition of stack routines with a fixed register file.
The transition between routines is an explicit jump and costs one step. -/
namespace Counting.StackMachine

/-- A common register count makes routine composition type preserving. -/
structure Routine (extraRegisters : Nat) where
  states : Nat
  code : Fin (states+1) → Instruction (extraRegisters+2) (states+1)

abbrev Routine.program {registers : Nat} (routine : Routine registers) : Program :=
  ⟨registers,routine.states,routine.code⟩

abbrev Routine.ofProgram (program : Program) : Routine program.extraRegisters :=
  ⟨program.states,program.code⟩

def Instruction.relabel {registers states targets : Nat} (label : Fin states → Fin targets) :
    Instruction registers states → Instruction registers targets
  | .halt => .halt
  | .jump next => .jump (label next)
  | .push register bit next => .push register bit (label next)
  | .pop register empty zero one => .pop register (label empty) (label zero) (label one)

namespace Routine

def leftControl {registers : Nat} (first second : Routine registers) (control : Control first.program) :
    Fin (first.states+second.states+2) := ⟨control.val,by have bounded := control.isLt; change control.val < first.states+1 at bounded; omega⟩

def rightControl {registers : Nat} (first second : Routine registers) (control : Control second.program) :
    Fin (first.states+second.states+2) := ⟨first.states+1+control.val,by have bounded := control.isLt; change control.val < second.states+1 at bounded; omega⟩

def sequence {registers : Nat} (first second : Routine registers) : Routine registers where
  states := first.states+second.states+1
  code control :=
    if inside : control.val < first.states+1 then
      match first.code ⟨control.val,inside⟩ with
      | .halt => .jump (rightControl first second 0)
      | instruction => instruction.relabel (leftControl first second)
    else
      (second.code ⟨control.val-(first.states+1),by have := control.isLt; omega⟩).relabel (rightControl first second)

def leftConfig {registers : Nat} (first second : Routine registers) (config : Config first.program) :
    Config (sequence first second).program := ⟨leftControl first second config.control,config.store⟩

def rightConfig {registers : Nat} (first second : Routine registers) (config : Config second.program) :
    Config (sequence first second).program := ⟨rightControl first second config.control,config.store⟩

theorem sequence_left_code {registers : Nat} (first second : Routine registers) (control : Control first.program) :
    (sequence first second).code (leftControl first second control) =
      match first.code control with
      | .halt => .jump (rightControl first second 0)
      | instruction => instruction.relabel (leftControl first second) := by
  simp only [sequence,leftControl,dif_pos control.isLt]

theorem sequence_right_code {registers : Nat} (first second : Routine registers) (control : Control second.program) :
    (sequence first second).code (rightControl first second control) =
      (second.code control).relabel (rightControl first second) := by
  have outside : ¬first.states+1+control.val < first.states+1 := by omega
  simp only [sequence,rightControl,dif_neg outside,Nat.add_sub_cancel_left]

theorem left_step {registers : Nat} (first second : Routine registers) (config next : Config first.program)
    (success : step first.program config = some next) :
    step (sequence first second).program (leftConfig first second config) = some (leftConfig first second next) := by
  unfold step at success ⊢
  dsimp only [leftConfig,program] at success ⊢
  rw [sequence_left_code]
  cases instruction : first.code config.control with
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

theorem left_halt {registers : Nat} (first second : Routine registers) (config : Config first.program)
    (halted : step first.program config = none) :
    step (sequence first second).program (leftConfig first second config) =
      some (rightConfig first second ⟨0,config.store⟩) := by
  have stop : first.code config.control = .halt := by
    cases instruction : first.code config.control <;> simp_all [step,program]
    split at halted <;> contradiction
  unfold step
  dsimp only [leftConfig,program]
  rw [sequence_left_code,stop]
  rfl

theorem right_step {registers : Nat} (first second : Routine registers) (config : Config second.program) :
    step (sequence first second).program (rightConfig first second config) =
      (step second.program config).map (rightConfig first second) := by
  unfold step
  dsimp only [rightConfig,program]
  rw [sequence_right_code]
  cases instruction : second.code config.control <;>
    simp only [program,Instruction.relabel,rightConfig,Option.map_none,Option.map_some]
  split <;> simp only [Option.map_some,rightConfig]
  split <;> rfl

theorem left_run {registers : Nat} (first second : Routine registers) (steps : Nat)
    {start finish : Config first.program} (success : Machine.run (step first.program) steps start = some finish) :
    Machine.run (step (sequence first second).program) steps (leftConfig first second start) =
      some (leftConfig first second finish) := by
  induction steps generalizing start with
  | zero => have equal := Option.some.inj success; subst finish; rfl
  | succ steps ih =>
      cases next : step first.program start with
      | none => simp only [Machine.run,next,Option.bind_none] at success; contradiction
      | some middle =>
          have tail : Machine.run (step first.program) steps middle = some finish := by
            simpa only [Machine.run,next,Option.bind_some] using success
          rw [Machine.run,left_step first second start middle next,Option.bind_some]
          exact ih tail

theorem right_run {registers : Nat} (first second : Routine registers) (steps : Nat) (start : Config second.program) :
    Machine.run (step (sequence first second).program) steps (rightConfig first second start) =
      (Machine.run (step second.program) steps start).map (rightConfig first second) :=
  (Machine.run_simulation _ _ _ (fun config => (right_step first second config).symm) steps start).symm

theorem sequence_run {registers : Nat} (first second : Routine registers)
    (firstSteps secondSteps : Nat) (store : Fin (registers+2) → List Bool)
    (middle : Config first.program) (last : Config second.program)
    (firstRun : Machine.run (step first.program) firstSteps ⟨0,store⟩ = some middle)
    (firstHalt : step first.program middle = none)
    (secondRun : Machine.run (step second.program) secondSteps ⟨0,middle.store⟩ = some last) :
    Machine.run (step (sequence first second).program) (firstSteps+1+secondSteps) ⟨0,store⟩ =
      some (rightConfig first second last) := by
  change Machine.run (step (sequence first second).program) _ (leftConfig first second ⟨0,store⟩) = _
  rw [show firstSteps+1+secondSteps = firstSteps+(secondSteps+1) by omega,Machine.run_add,
    left_run first second firstSteps firstRun,Option.bind_some,Machine.run,
    left_halt first second middle firstHalt,Option.bind_some,right_run,secondRun]
  rfl

end Routine
end Counting.StackMachine
