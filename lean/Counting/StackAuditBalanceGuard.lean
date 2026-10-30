import Counting.StackAuditBalanceAt
import Counting.StackEncodingGuards
import Counting.StackRoutineMove
import Counting.AuditBalanceSpec

namespace Counting.StackMachine.AuditBalance
open Routine RealizabilityCheck EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

abbrev guardAt : Routine 40 := sequence checkAt
  (sequence (move 39 0 1 41) (ofProgram (combineFlagsProgram 40 1)))

/-- Accumulate a balance comparison into the existing audit status,
preserving its tail as well as both complete encoded inputs. -/
theorem guardAt_executes (vista : Executable.Vista) (weights : Array Nat)
    (valid : vista.valid=true) (length : weights.size=vista.nodes.size)
    (round old : Nat) (accepted : Bool) (tail : List Bool) :
    ∃ time ≤ 100000200*((Encoding.vista.encode vista).length+
        ((Encoding.array Encoding.natural).encode weights).length+(round+1).size+old.size+2)^15,
      Executes guardAt
        (massFile (Encoding.vista.encode vista) ((Encoding.array Encoding.natural).encode weights)
          (round+1).bits [] old.bits (accepted::tail) [] [] []) time
        (massFile (Encoding.vista.encode vista) ((Encoding.array Encoding.natural).encode weights)
          (round+1).bits [] old.bits
          ((accepted && Executable.auditBalanceAt vista weights round old)::tail) [] [] []) := by
  let source := Encoding.vista.encode vista
  let encoded := (Encoding.array Encoding.natural).encode weights
  let answer := Executable.auditBalanceAt vista weights round old
  obtain ⟨time,bounded,a⟩ := checkAt_actual vista weights valid length round old accepted tail
  let checked := balanceFile source encoded (round+1).bits old.bits (accepted::tail) [answer]
  have b := move_executes 39 (0:Fin 42) 1 41 (by decide) (by decide) (by decide) checked
    (by simp [checked,balanceFile,massFile])
  have sourceAt : checked 0=[answer] := by simp [checked,balanceFile]
  have statusAt : checked 1=accepted::tail := by simp [checked,balanceFile,massFile]
  rw [sourceAt,statusAt] at b
  let combined := massFile source encoded (round+1).bits [] old.bits
    (answer::accepted::tail) [] [] []
  have bResult : Function.update (Function.update checked 1 ([answer]++accepted::tail)) 0 []=combined := by
    funext r
    fin_cases r <;> simp [checked,balanceFile,massFile,combined]
  rw [bResult] at b
  have c := combineFlags_executes 40 (1:Fin 42) combined accepted answer tail (by simp [combined,massFile])
  have cResult : Function.update combined 1 ((accepted && answer)::tail)=
      massFile source encoded (round+1).bits [] old.bits ((accepted && answer)::tail) [] [] [] := by
    funext r
    fin_cases r <;> simp [combined,massFile]
  rw [cResult] at c
  refine ⟨_,?_,a.sequence (b.sequence c)⟩
  have positive : 1 ≤ ((Encoding.vista.encode vista).length+
      ((Encoding.array Encoding.natural).encode weights).length+(round+1).size+old.size+2)^15 :=
    Nat.one_le_pow _ _ (by omega)
  simp only [List.length_cons,List.length_nil]
  omega

end Counting.StackMachine.AuditBalance
