import Counting.StackRoutineBasic

namespace Counting.StackMachine.Routine
set_option backward.isDefEq.respectTransparency false

def nonemptyYesControl {registers : Nat} (yes no : Routine registers) (control : Control yes.program) :
    Fin (yes.states+no.states+6) := ⟨4+control.val,by have:=control.isLt;change control.val<yes.states+1 at this;omega⟩

def nonemptyNoControl {registers : Nat} (yes no : Routine registers) (control : Control no.program) :
    Fin (yes.states+no.states+6) := ⟨yes.states+5+control.val,by have:=control.isLt;change control.val<no.states+1 at this;omega⟩

/-- Inspect list emptiness, restoring either possible leading bit before
the nonempty branch. No scratch register or canonical-word assumption is used. -/
def branchNonempty {registers : Nat} (source : Fin (registers+2)) (yes no : Routine registers) : Routine registers where
  states:=yes.states+no.states+5
  code control:=
    if control.val=0 then .pop source (nonemptyNoControl yes no 0) ⟨1,by omega⟩ ⟨2,by omega⟩
    else if control.val=1 then .push source false ⟨3,by omega⟩
    else if control.val=2 then .push source true ⟨3,by omega⟩
    else if control.val=3 then .jump (nonemptyYesControl yes no 0)
    else if inside : control.val<yes.states+5 then
      (yes.code ⟨control.val-4,by omega⟩).relabel (nonemptyYesControl yes no)
    else (no.code ⟨control.val-(yes.states+5),by have:=control.isLt;omega⟩).relabel (nonemptyNoControl yes no)

def nonemptyYesConfig {registers : Nat} (source : Fin (registers+2)) (yes no : Routine registers)
    (config : Config yes.program) : Config (branchNonempty source yes no).program :=
  ⟨nonemptyYesControl yes no config.control,config.store⟩

def nonemptyNoConfig {registers : Nat} (source : Fin (registers+2)) (yes no : Routine registers)
    (config : Config no.program) : Config (branchNonempty source yes no).program :=
  ⟨nonemptyNoControl yes no config.control,config.store⟩

theorem nonempty_yes_code {registers : Nat} (source : Fin (registers+2)) (yes no : Routine registers)
    (control : Control yes.program) :
    (branchNonempty source yes no).code (nonemptyYesControl yes no control)=
      (yes.code control).relabel (nonemptyYesControl yes no) := by
  have inside : 4+control.val<yes.states+5 := by have:=control.isLt;change control.val<yes.states+1 at this;omega
  simp only [branchNonempty,nonemptyYesControl,show ¬4+control.val=0 by omega,
    show ¬4+control.val=1 by omega,show ¬4+control.val=2 by omega,
    show ¬4+control.val=3 by omega,if_false,dif_pos inside,Nat.add_sub_cancel_left]

theorem nonempty_no_code {registers : Nat} (source : Fin (registers+2)) (yes no : Routine registers)
    (control : Control no.program) :
    (branchNonempty source yes no).code (nonemptyNoControl yes no control)=
      (no.code control).relabel (nonemptyNoControl yes no) := by
  simp only [branchNonempty,nonemptyNoControl,show ¬yes.states+5+control.val=0 by omega,
    show ¬yes.states+5+control.val=1 by omega,show ¬yes.states+5+control.val=2 by omega,
    show ¬yes.states+5+control.val=3 by omega,if_false,
    dif_neg (show ¬yes.states+5+control.val<yes.states+5 by omega),Nat.add_sub_cancel_left]

theorem nonempty_yes_step {registers : Nat} (source : Fin (registers+2)) (yes no : Routine registers)
    (config : Config yes.program) :
    step (branchNonempty source yes no).program (nonemptyYesConfig source yes no config)=
      (step yes.program config).map (nonemptyYesConfig source yes no) := by
  unfold step
  dsimp only [nonemptyYesConfig,program]
  rw [nonempty_yes_code]
  cases instruction:yes.code config.control <;>
    simp only [Instruction.relabel,nonemptyYesConfig,Option.map_none,Option.map_some]
  try rfl
  split <;> simp only [Option.map_some,nonemptyYesConfig]
  split <;> rfl

theorem nonempty_no_step {registers : Nat} (source : Fin (registers+2)) (yes no : Routine registers)
    (config : Config no.program) :
    step (branchNonempty source yes no).program (nonemptyNoConfig source yes no config)=
      (step no.program config).map (nonemptyNoConfig source yes no) := by
  unfold step
  dsimp only [nonemptyNoConfig,program]
  rw [nonempty_no_code]
  cases instruction:no.code config.control <;>
    simp only [Instruction.relabel,nonemptyNoConfig,Option.map_none,Option.map_some]
  try rfl
  split <;> simp only [Option.map_some,nonemptyNoConfig]
  split <;> rfl

theorem branchNonempty_empty {registers : Nat} (source : Fin (registers+2)) (yes no : Routine registers)
    (store result : Store registers) (time : Nat) (empty : store source=[])
    (executed : Executes no store time result) :
    Executes (branchNonempty source yes no) store (1+time) result := by
  obtain ⟨finish,ran,halted,output⟩:=executed
  have first : Machine.run (step (branchNonempty source yes no).program) 1 ⟨0,store⟩=
      some (nonemptyNoConfig source yes no ⟨0,store⟩) := by
    simp [Machine.run,step,branchNonempty,empty,nonemptyNoConfig]
  have simulation:=Machine.run_simulation _ _ _
    (fun config=>(nonempty_no_step source yes no config).symm) time (⟨0,store⟩ : Config no.program)
  refine ⟨nonemptyNoConfig source yes no finish,?_,?_,output⟩
  · rw [Machine.run_add,first,Option.bind_some,←simulation,ran]
    rfl
  · rw [nonempty_no_step,halted]
    rfl

theorem branchNonempty_cons {registers : Nat} (source : Fin (registers+2)) (yes no : Routine registers)
    (store result : Store registers) (bit : Bool) (tail : List Bool) (time : Nat)
    (nonempty : store source=bit::tail) (executed : Executes yes store time result) :
    Executes (branchNonempty source yes no) store (time+3) result := by
  obtain ⟨finish,ran,halted,output⟩:=executed
  have restore : Function.update (Function.update store source tail) source (bit::tail)=store := by
    rw [Function.update_idem,←nonempty,Function.update_eq_self]
  have first : Machine.run (step (branchNonempty source yes no).program) 3 ⟨0,store⟩=
      some (nonemptyYesConfig source yes no ⟨0,store⟩) := by
    cases bit <;> simp [Machine.run,step,branchNonempty,nonempty,nonemptyYesConfig,restore]
  have simulation:=Machine.run_simulation _ _ _
    (fun config=>(nonempty_yes_step source yes no config).symm) time (⟨0,store⟩ : Config yes.program)
  refine ⟨nonemptyYesConfig source yes no finish,?_,?_,output⟩
  · rw [show time+3=3+time by omega,Machine.run_add,first,Option.bind_some,←simulation,ran]
    rfl
  · rw [nonempty_yes_step,halted]
    rfl

end Counting.StackMachine.Routine
