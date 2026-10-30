import Counting.StackAuditPositive
import Counting.StackAuditSumSpec

namespace Counting.StackMachine.AuditCandidate
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

def file (input output candidate values : List Bool) : Store 34 :=
  fun r=>if r=0 then input else if r=1 then output else if r=32 then candidate else if r=33 then values else []

def positiveRoles : Fin 32 ↪ Fin 36 :=
  ⟨fun r=>⟨r.val,by omega⟩,by intro a b equal;exact Fin.ext (congrArg (fun r:Fin 36=>r.val) equal)⟩
def sumRoles : Fin 24 ↪ Fin 36 :=
  ⟨fun r=>if r=21 then 32 else if r=22 then 33 else ⟨r.val,by omega⟩,by decide⟩

abbrev convertPositive : Routine 34 := relocate AuditPositive.routine positiveRoles
abbrev checkSum : Routine 34 := relocate AuditSum.check sumRoles

theorem convertPositive_executes (values : Option (Array Rat)) (candidate : List Bool) :
    ∃ time≤400000*((AuditPositive.inputWord values).length+1)^3,
      Executes convertPositive (file (AuditPositive.inputWord values) [] candidate []) time
        (file [] (AuditPositive.outputWord values) candidate []) := by
  obtain ⟨time,bounded,ran⟩ := AuditPositive.routine_executes values
  refine ⟨time,bounded,?_⟩
  apply relocate_executes_frame AuditPositive.routine positiveRoles _ _ _ _ time _ _ _ ran
  · funext r;fin_cases r <;> simp [positiveRoles,file,inputStore]
  · intro r;fin_cases r <;> simp [positiveRoles,file,outputStore]
  · intro r outside
    have r0 : r≠0 := by intro eq;subst r;exact outside 0 rfl
    have r1 : r≠1 := by intro eq;subst r;exact outside 1 rfl
    simp [file,r0,r1]

theorem checkSum_executes (natural : Array Nat) (candidate : Nat) :
    ∃ time≤3000*(((Encoding.array Encoding.natural).encode natural).length+candidate.size+1)^3,
      Executes checkSum (file [] [] candidate.bits ((Encoding.array Encoding.natural).encode natural)) time
        (file [] [AuditSum.accepts natural.toList candidate] candidate.bits
          ((Encoding.array Encoding.natural).encode natural)) := by
  obtain ⟨time,bounded,ran⟩ := AuditSum.check_executes natural.toList candidate
  refine ⟨time,bounded,?_⟩
  apply relocate_executes_frame AuditSum.check sumRoles _ _ _ _ time _ _ _ ran
  · funext r;fin_cases r <;> simp [sumRoles,file,AuditSum.file,Encoding.array,Encoding.transport]
  · intro r;fin_cases r <;> simp [sumRoles,file,AuditSum.file,Encoding.array,Encoding.transport]
  · intro r outside
    have r1 : r≠1 := by intro eq;subst r;exact outside 1 rfl
    simp [file,r1]

end Counting.StackMachine.AuditCandidate
