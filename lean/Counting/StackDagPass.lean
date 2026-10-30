import Counting.StackDagSemanticSpec

/-! A reusable semantic pass retains the original encoded input outside the
35 working registers. Copying and clearing the per-pass source are charged;
register relocation is the verified finite-control address transformation. -/
namespace Counting.StackMachine.DagValidation
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

def scanStore (input flags : List Bool) : Store 33:=fun r=>if r=17 then input else if r=1 then flags else []
def validatorStore (input flags : List Bool) : Store 35:=fun r=>if r=35 then input else if r=1 then flags else []

def validationRoles : Fin 35 ↪ Fin 37 where
  toFun r:=⟨r.val,by omega⟩
  inj':=by intro a b same;apply Fin.ext;exact congrArg (fun r:Fin 37=>r.val) same

def validationPass (routine : Routine 33) : Routine 35:=
  sequence (ofProgram (ListPrograms.copyProgram 34 35 17 36))
    (sequence (mapRegisters validationRoles routine) (clear 17))

theorem validationPass_executes (routine : Routine 33) (input rest before after : List Bool)
    (time : Nat) (ran : Executes routine (scanStore input before) time (scanStore rest after)) :
    Executes (validationPass routine) (validatorStore input before)
      (5*input.length+2+1+(time+1+(rest.length+1))) (validatorStore input after):=by
  have copying:=copy_executes 34 35 17 36 (by decide) (by decide) (by decide) (validatorStore input before)
    (by simp [validatorStore])
  simp only [validatorStore,ite_true,
    show (17:Fin 37)≠35 by decide,show (17:Fin 37)≠1 by decide,if_false,List.append_nil] at copying
  let copied:=Function.update (validatorStore input before) 17 input
  let result:=Function.update (validatorStore input after) 17 rest
  have relocated : Executes (mapRegisters validationRoles routine) copied time result:=by
    apply relocate_executes_frame routine validationRoles copied result (scanStore input before)
      (scanStore rest after) time _ _ _ ran
    · funext r;fin_cases r <;> simp [copied,validatorStore,scanStore,validationRoles]
    · intro r;fin_cases r <;> simp [result,validatorStore,scanStore,validationRoles]
    · intro r outside
      have n1 : r≠1:=by intro same;subst r;exact outside 1 rfl
      have n17 : r≠17:=by intro same;subst r;exact outside 17 rfl
      simp [result,copied,validatorStore,n1,n17]
  have clearing:=clear_executes (17:Fin 37) result
  have suffix : result 17=rest:=by simp [result]
  rw [suffix] at clearing
  have final : Function.update result 17 []=validatorStore input after:=by
    funext r
    by_cases same : r=17
    · subst r;simp [validatorStore]
    · simp [result,same]
  rw [final] at clearing
  exact copying.sequence (relocated.sequence clearing)

@[simp] theorem vista_code_list (vista : Executable.Vista) :
    Encoding.vista.encode vista=(Encoding.list Encoding.node).encode vista.nodes.toList++Encoding.natural.encode vista.bottom:=rfl

def tableSuffix (vista : Executable.Vista) : List Bool:=
  Encoding.sequence Encoding.node vista.nodes.toList++Encoding.natural.encode vista.bottom

theorem tableSuffix_length (vista : Executable.Vista) : (tableSuffix vista).length≤(Encoding.vista.encode vista).length:=by
  rw [vista_code_list]
  change (Encoding.sequence Encoding.node vista.nodes.toList++Encoding.natural.encode vista.bottom).length≤
    ((Encoding.natural.encode vista.nodes.toList.length++Encoding.sequence Encoding.node vista.nodes.toList)++Encoding.natural.encode vista.bottom).length
  simp only [List.length_append]
  omega

end Counting.StackMachine.DagValidation
