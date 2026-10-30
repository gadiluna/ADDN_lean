import Counting.StackAuditBalanceGuard
import Counting.StackAuditPropagationSelect
import Counting.StackRoutineUnary

namespace Counting.StackMachine.AuditBalance
open Routine RealizabilityCheck
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

/-- The first forty-two registers are the mass-scan workspace; eight
additional registers retain the traversal state during every checked sum. -/
def bankFile (source weights target query status : List Bool) (saved : Fin 8 → List Bool) : Store 48 :=
  fun r=>if h:r.val<42 then massFile source weights target [] query status [] [] [] ⟨r.val,h⟩
    else saved ⟨r.val-42,by omega⟩

def massRoles : Fin 42 ↪ Fin 50 :=
  ⟨fun r=>⟨r.val,by omega⟩,by intro a b equal;exact Fin.ext (congrArg (fun r:Fin 50=>r.val) equal)⟩

abbrev bankGuard : Routine 48 := relocate guardAt massRoles

theorem bankGuard_executes (vista : Executable.Vista) (weights : Array Nat)
    (valid : vista.valid=true) (length : weights.size=vista.nodes.size)
    (round old : Nat) (accepted : Bool) (tail : List Bool) (saved : Fin 8 → List Bool) :
    ∃ time ≤ 100000200*((Encoding.vista.encode vista).length+
        ((Encoding.array Encoding.natural).encode weights).length+(round+1).size+old.size+2)^15,
      Executes bankGuard
        (bankFile (Encoding.vista.encode vista) ((Encoding.array Encoding.natural).encode weights)
          (round+1).bits old.bits (accepted::tail) saved) time
        (bankFile (Encoding.vista.encode vista) ((Encoding.array Encoding.natural).encode weights)
          (round+1).bits old.bits
          ((accepted && Executable.auditBalanceAt vista weights round old)::tail) saved) := by
  obtain ⟨time,bounded,executed⟩ := guardAt_executes vista weights valid length round old accepted tail
  refine ⟨time,bounded,?_⟩
  apply relocate_executes_frame guardAt massRoles _ _ _ _ time _ _ _ executed
  · funext r
    simp [bankFile,massRoles,r.isLt]
  · intro r
    simp [bankFile,massRoles,r.isLt]
  · intro r outside
    have beyond : ¬r.val<42 := by
      intro inside
      exact outside ⟨r.val,inside⟩ (by apply Fin.ext;rfl)
    simp [bankFile,beyond]

/-- A traversal index already has bounded unary length. Only this copied
counter is converted to binary for the mass scan; no binary label is expanded. -/
abbrev prepareQuery : Routine 48 := sequence (ofProgram (ListPrograms.copyProgram 47 43 26 4))
  (ofProgram (Unary.toBinaryProgram 47 26 36 4))

theorem prepareQuery_executes (store : Store 48) (index : Nat)
    (counter : store 43=List.replicate index true) (e4 : store 4=[]) (e26 : store 26=[]) (e36 : store 36=[]) :
    ∃ time ≤ 20*(index+1)^2,
      Executes prepareQuery store time (Function.update store 36 index.bits) := by
  have a := copy_executes 47 (43:Fin 50) 26 4 (by decide) (by decide) (by decide) store e4
  rw [counter,e26,List.append_nil,List.length_replicate] at a
  let copied := Function.update store 26 (List.replicate index true)
  obtain ⟨time,bounded,b⟩ := toBinary_executes 47 (26:Fin 50) 36 4 (by decide) (by decide) (by decide)
    copied 0 (by simp [copied,e36]) (by simp [copied,e4])
  have source : copied 26=List.replicate index true := by simp [copied]
  rw [source,List.length_replicate,Nat.zero_add] at b bounded
  have restored : Function.update (Function.update copied 26 []) 36 index.bits=Function.update store 36 index.bits := by
    simp only [copied,Function.update_idem]
    rw [←e26,Function.update_eq_self]
  rw [restored] at b
  refine ⟨_,?_,a.sequence b⟩
  nlinarith

end Counting.StackMachine.AuditBalance
