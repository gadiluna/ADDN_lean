import Counting.StackAuditPrefixInput
import Counting.StackDagValidator

namespace Counting.StackMachine.AuditPrefix
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

def validatorRoles : Fin 37 ↪ Fin 52 :=
  ⟨fun r=>⟨r.val,by omega⟩,by intro a b equal;exact Fin.ext (congrArg (fun r:Fin 52=>r.val) equal)⟩

abbrev validateStored : Routine 50 := sequence (ofProgram (ListPrograms.copyProgram 49 40 0 51))
  (relocate DagValidation.validationRoutine validatorRoles)

/-- Invoke the actual total DAG validator on a paid copy of the retained
vista word. Invalid canonical DAGs produce false; no validity is assumed. -/
theorem validateStored_executes (vista : Executable.Vista) (leaders candidate last : List Bool) :
    ∃ time ≤ 226000000*((Encoding.vista.encode vista).length+1)^6,
      Executes validateStored (inputFile [] leaders candidate last (Encoding.vista.encode vista)) time
        (Function.update (inputFile [] leaders candidate last (Encoding.vista.encode vista)) 1 [vista.valid]) := by
  let code:=Encoding.vista.encode vista
  let store:=inputFile [] leaders candidate last code
  have a:=copy_executes 49 (40:Fin 52) 0 51 (by decide) (by decide) (by decide) store rfl
  have source : store 40=code := rfl
  have target : store 0=[] := rfl
  rw [source,target,List.append_nil] at a
  let copied:=Function.update store 0 code
  obtain ⟨time,bound,run⟩:=DagValidation.validation_executes code
  rw [DagValidation.validWord_encoded] at run
  have projected : copied ∘ validatorRoles=inputStore 35 code := by
    funext r;fin_cases r <;> simp [copied,store,inputFile,validatorRoles,inputStore]
  let result:=Function.update store 1 [vista.valid]
  have b : Executes (relocate DagValidation.validationRoutine validatorRoles) copied time result := by
    apply relocate_executes_frame DagValidation.validationRoutine validatorRoles copied result
      (inputStore 35 code) (outputStore 35 [vista.valid]) time projected _ _ run
    · intro r;fin_cases r <;> simp [result,store,inputFile,validatorRoles,outputStore]
    · intro r outside
      have n0 : r≠0 := by intro equal;subst r;exact outside 0 rfl
      have n1 : r≠1 := by intro equal;subst r;exact outside 1 rfl
      simp [result,copied,n0,n1]
  refine ⟨_,?_,a.sequence b⟩
  have linear : code.length+1 ≤ (code.length+1)^6 := Nat.le_self_pow (by decide) _
  change 5*code.length+2+1+time ≤ 226000000*(code.length+1)^6
  omega

abbrev prepareValidated : Routine 50 := sequence readInput validateStored

/-- Actual input parsing and DAG validation, retaining all binary
parameters for the remaining prefix guards and bounded scans. -/
theorem prepareValidated_executes (vista : Executable.Vista) (leaders candidate last : Nat) :
    ∃ time ≤ 227000000*((inputWord vista leaders candidate last).length+1)^6,
      Executes prepareValidated (inputStore 50 (inputWord vista leaders candidate last)) time
        (Function.update (inputFile [] leaders.bits candidate.bits last.bits (Encoding.vista.encode vista))
          1 [vista.valid]) := by
  obtain ⟨inputTime,inputBound,a⟩:=readInput_executes vista leaders candidate last
  obtain ⟨validationTime,validationBound,b⟩:=validateStored_executes vista leaders.bits candidate.bits last.bits
  refine ⟨_,?_,a.sequence b⟩
  have codeLength : (Encoding.vista.encode vista).length ≤ (inputWord vista leaders candidate last).length := by
    rw [inputWord_length]
    omega
  let L:=(inputWord vista leaders candidate last).length+1
  have positive : 1 ≤ L := by dsimp only [L];omega
  have inputRaised : inputTime ≤ 100*L^6 := inputBound.trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right positive (by decide)))
  have validationRaised : validationTime ≤ 226000000*L^6 := validationBound.trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by dsimp only [L];omega) 6))
  have one : 1 ≤ L^6 := Nat.one_le_pow _ _ positive
  change inputTime+1+validationTime ≤ 227000000*L^6
  omega

end Counting.StackMachine.AuditPrefix
