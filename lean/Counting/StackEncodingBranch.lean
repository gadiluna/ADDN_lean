import Counting.StackRoutineSemantics

/-! A real finite-control conditional for compositional codec programs. One
pop consumes the condition, then control enters exactly one selected routine.
An empty condition takes the false branch. -/
namespace Counting.StackMachine.EncodingPrograms

set_option backward.isDefEq.respectTransparency false

def branchYesControl {extra : Nat} (yes no : Routine extra) (control : Control yes.program) :
    Fin (yes.states+no.states+3) := ⟨1+control.val,by have := control.isLt; change control.val<yes.states+1 at this; omega⟩

def branchNoControl {extra : Nat} (yes no : Routine extra) (control : Control no.program) :
    Fin (yes.states+no.states+3) := ⟨yes.states+2+control.val,by have := control.isLt; change control.val<no.states+1 at this; omega⟩

def branchRoutine {extra : Nat} (flag : Fin (extra+2)) (yes no : Routine extra) : Routine extra where
  states := yes.states+no.states+2
  code control :=
    if zero : control.val=0 then
      .pop flag (branchNoControl yes no 0) (branchNoControl yes no 0) (branchYesControl yes no 0)
    else if inside : control.val<yes.states+2 then
      (yes.code ⟨control.val-1,by omega⟩).relabel (branchYesControl yes no)
    else
      (no.code ⟨control.val-(yes.states+2),by have:=control.isLt; omega⟩).relabel (branchNoControl yes no)

def branchYesConfig {extra : Nat} (flag : Fin (extra+2)) (yes no : Routine extra)
    (config : Config yes.program) : Config (branchRoutine flag yes no).program :=
  ⟨branchYesControl yes no config.control,config.store⟩

def branchNoConfig {extra : Nat} (flag : Fin (extra+2)) (yes no : Routine extra)
    (config : Config no.program) : Config (branchRoutine flag yes no).program :=
  ⟨branchNoControl yes no config.control,config.store⟩

theorem branch_yes_code {extra : Nat} (flag : Fin (extra+2)) (yes no : Routine extra)
    (control : Control yes.program) :
    (branchRoutine flag yes no).code (branchYesControl yes no control) =
      (yes.code control).relabel (branchYesControl yes no) := by
  have positive : 1+control.val≠0 := by omega
  have inside : 1+control.val<yes.states+2 := by have:=control.isLt; change control.val<yes.states+1 at this; omega
  simp only [branchRoutine,branchYesControl,dif_neg positive,dif_pos inside,Nat.add_sub_cancel_left]

theorem branch_no_code {extra : Nat} (flag : Fin (extra+2)) (yes no : Routine extra)
    (control : Control no.program) :
    (branchRoutine flag yes no).code (branchNoControl yes no control) =
      (no.code control).relabel (branchNoControl yes no) := by
  have positive : yes.states+2+control.val≠0 := by omega
  have outside : ¬yes.states+2+control.val<yes.states+2 := by omega
  simp only [branchRoutine,branchNoControl,dif_neg positive,dif_neg outside,Nat.add_sub_cancel_left]

theorem branch_yes_step {extra : Nat} (flag : Fin (extra+2)) (yes no : Routine extra)
    (config : Config yes.program) :
    step (branchRoutine flag yes no).program (branchYesConfig flag yes no config) =
      (step yes.program config).map (branchYesConfig flag yes no) := by
  unfold step
  dsimp only [branchYesConfig,Routine.program]
  rw [branch_yes_code]
  cases instruction : yes.code config.control <;>
    simp only [Instruction.relabel,branchYesConfig,Option.map_none,Option.map_some]
  try rfl
  split <;> simp only [Option.map_some,branchYesConfig]
  split <;> rfl

theorem branch_no_step {extra : Nat} (flag : Fin (extra+2)) (yes no : Routine extra)
    (config : Config no.program) :
    step (branchRoutine flag yes no).program (branchNoConfig flag yes no config) =
      (step no.program config).map (branchNoConfig flag yes no) := by
  unfold step
  dsimp only [branchNoConfig,Routine.program]
  rw [branch_no_code]
  cases instruction : no.code config.control <;>
    simp only [Instruction.relabel,branchNoConfig,Option.map_none,Option.map_some]
  try rfl
  split <;> simp only [Option.map_some,branchNoConfig]
  split <;> rfl

theorem branch_yes_run {extra : Nat} (flag : Fin (extra+2)) (yes no : Routine extra)
    (time : Nat) (config : Config yes.program) :
    Machine.run (step (branchRoutine flag yes no).program) time (branchYesConfig flag yes no config) =
      (Machine.run (step yes.program) time config).map (branchYesConfig flag yes no) :=
  (Machine.run_simulation _ _ _ (fun config => (branch_yes_step flag yes no config).symm) time config).symm

theorem branch_no_run {extra : Nat} (flag : Fin (extra+2)) (yes no : Routine extra)
    (time : Nat) (config : Config no.program) :
    Machine.run (step (branchRoutine flag yes no).program) time (branchNoConfig flag yes no config) =
      (Machine.run (step no.program) time config).map (branchNoConfig flag yes no) :=
  (Machine.run_simulation _ _ _ (fun config => (branch_no_step flag yes no config).symm) time config).symm

theorem branch_executes_true {extra : Nat} (flag : Fin (extra+2)) (yes no : Routine extra)
    (store result : Routine.Store extra) (tail : List Bool) (time : Nat)
    (condition : store flag=true::tail)
    (body : Routine.Executes yes (Function.update store flag tail) time result) :
    Routine.Executes (branchRoutine flag yes no) store (1+time) result := by
  obtain ⟨finish,executed,halted,output⟩:=body
  refine ⟨branchYesConfig flag yes no finish,?_,?_,output⟩
  · have first : Machine.run (step (branchRoutine flag yes no).program) 1 ⟨0,store⟩ =
        some (branchYesConfig flag yes no ⟨0,Function.update store flag tail⟩) := by
      simp [Machine.run,step,branchRoutine,condition,branchYesConfig]
    rw [Machine.run_add,first,Option.bind_some,branch_yes_run,executed]
    rfl
  · rw [branch_yes_step,halted]
    rfl

theorem branch_executes_false {extra : Nat} (flag : Fin (extra+2)) (yes no : Routine extra)
    (store result : Routine.Store extra) (tail : List Bool) (time : Nat)
    (condition : store flag=false::tail)
    (body : Routine.Executes no (Function.update store flag tail) time result) :
    Routine.Executes (branchRoutine flag yes no) store (1+time) result := by
  obtain ⟨finish,executed,halted,output⟩:=body
  refine ⟨branchNoConfig flag yes no finish,?_,?_,output⟩
  · have first : Machine.run (step (branchRoutine flag yes no).program) 1 ⟨0,store⟩ =
        some (branchNoConfig flag yes no ⟨0,Function.update store flag tail⟩) := by
      simp [Machine.run,step,branchRoutine,condition,branchNoConfig]
    rw [Machine.run_add,first,Option.bind_some,branch_no_run,executed]
    rfl
  · rw [branch_no_step,halted]
    rfl

theorem branch_executes_empty {extra : Nat} (flag : Fin (extra+2)) (yes no : Routine extra)
    (store result : Routine.Store extra) (time : Nat)
    (condition : store flag=[])
    (body : Routine.Executes no store time result) :
    Routine.Executes (branchRoutine flag yes no) store (1+time) result := by
  obtain ⟨finish,executed,halted,output⟩:=body
  refine ⟨branchNoConfig flag yes no finish,?_,?_,output⟩
  · have first : Machine.run (step (branchRoutine flag yes no).program) 1 ⟨0,store⟩ =
        some (branchNoConfig flag yes no ⟨0,store⟩) := by
      simp [Machine.run,step,branchRoutine,condition,branchNoConfig]
    rw [Machine.run_add,first,Option.bind_some,branch_no_run,executed]
    rfl
  · rw [branch_no_step,halted]
    rfl

end Counting.StackMachine.EncodingPrograms
