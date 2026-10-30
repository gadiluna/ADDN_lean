import Counting.StackDagPasses
import Counting.StackEncodingDagMachine
import Counting.StackRoutineClean

namespace Counting.StackMachine.DagValidation
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

def syntaxRoles : Fin 17 ↪ Fin 37 where
  toFun r:=⟨r.val,by omega⟩
  inj':=by intro a b same;apply Fin.ext;exact congrArg (fun r:Fin 37=>r.val) same

def syntaxGate : Routine 35:=mapRegisters syntaxRoles (isolate DagParser.vista.recognition)

def validatorStart (input : List Bool) : Store 35:=Function.update (validatorStore input []) 0 input

theorem syntaxGate_executes (input : List Bool) :
    ∃ time ≤ 70500*(input.length+1)^4,
      Executes syntaxGate (validatorStart input) time
        (validatorStore input [(Encoding.vista.decodeExact input).isSome]):=by
  obtain ⟨time,bound,ran⟩:=isolate_executes DagParser.vista.recognition
    (fun input=>[(Encoding.vista.decodeExact input).isSome]) (Complexity.polynomial 3910 4)
    DagParser.vista_serialization_computes input
  have moved : Executes syntaxGate (validatorStart input) time
      (validatorStore input [(Encoding.vista.decodeExact input).isSome]):=by
    apply relocate_executes_frame (isolate DagParser.vista.recognition) syntaxRoles (validatorStart input)
      (validatorStore input [(Encoding.vista.decodeExact input).isSome])
      (inputStore 15 input) (outputStore 15 [(Encoding.vista.decodeExact input).isSome]) time _ _ _ ran
    · funext r;fin_cases r <;> simp [validatorStart,validatorStore,inputStore,syntaxRoles]
    · intro r;fin_cases r <;> simp [validatorStore,outputStore,syntaxRoles]
    · intro r outside
      have n0 : r≠0:=by intro same;subst r;exact outside 0 rfl
      have n1 : r≠1:=by intro same;subst r;exact outside 1 rfl
      simp [validatorStart,validatorStore,n0,n1]
  have linear:=Nat.le_self_pow (by decide : 4≠0) (input.length+1)
  change time≤18*(3910*(input.length+1)^4+input.length+3) at bound
  exact ⟨time,by omega,moved⟩

def semanticOnValid : Routine 35:=sequence (pushBit 1 true) semanticRoutine

theorem semanticOnValid_executes (vista : Executable.Vista) :
    ∃ time ≤ 224000010*((Encoding.vista.encode vista).length+1)^6,
      Executes semanticOnValid (validatorStore (Encoding.vista.encode vista) []) time
        (validatorStore (Encoding.vista.encode vista) [vista.valid]):=by
  have starting:=pushBit_executes (1:Fin 37) true (validatorStore (Encoding.vista.encode vista) [])
  have initial : Function.update (validatorStore (Encoding.vista.encode vista) []) 1
      (true::validatorStore (Encoding.vista.encode vista) [] 1)=validatorStore (Encoding.vista.encode vista) [true]:=by
    funext r
    by_cases same : r=1 <;> simp [validatorStore,same]
  rw [initial] at starting
  obtain ⟨time,bound,ran⟩:=semanticRoutine_executes vista true []
  simp only [Bool.true_and] at ran
  have one : 1≤((Encoding.vista.encode vista).length+1)^6:=Nat.one_le_pow _ _ (by omega)
  exact ⟨1+1+time,by omega,starting.sequence ran⟩

end Counting.StackMachine.DagValidation
