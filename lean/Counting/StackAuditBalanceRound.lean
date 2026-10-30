import Counting.StackAuditBalanceLevel
import Counting.StackAuditBalanceNext

namespace Counting.StackMachine.AuditBalance
open Routine RealizabilityCheck
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

abbrev roundItem : Routine 48 := sequence prepareLevel (sequence levelLoop finishLevel)

def roundBudget (vista : Executable.Vista) (weights : Array Nat) (round : Nat) : Nat :=
  levelBudget vista weights round vista.nodes.size+6*vista.nodes.size+4*round.size+4*(round+1).size+21

/-- A full round check, including copying the stored-node budget, every
selected balance test, clearing the completed index, and binary increments. -/
theorem roundItem_executes (vista : Executable.Vista) (weights : Array Nat)
    (valid : vista.valid=true) (length : weights.size=vista.nodes.size)
    (round : Nat) (accepted : Bool) (tail : List Bool) (saved : Fin 8 → List Bool)
    (table : saved 0=Encoding.sequence Encoding.node vista.nodes.toList++Encoding.natural.encode vista.bottom)
    (indexEmpty : saved 1=[]) (query : saved 2=round.bits) (flag : saved 3=[])
    (counterEmpty : saved 4=[]) (scratch : saved 5=[]) (nodeCount : saved 7=List.replicate vista.nodes.size true) :
    ∃ time ≤ roundBudget vista weights round,
      Executes roundItem
        (bankFile (Encoding.vista.encode vista) ((Encoding.array Encoding.natural).encode weights)
          (round+1).bits [] (accepted::tail) saved) time
        (bankFile (Encoding.vista.encode vista) ((Encoding.array Encoding.natural).encode weights)
          (round+2).bits [] ((accepted && Executable.auditBalanceLevel vista weights round)::tail)
          (Function.update saved 2 (round+1).bits)) := by
  let source := Encoding.vista.encode vista
  let encoded := (Encoding.array Encoding.natural).encode weights
  have a := prepareLevel_executes source encoded (round+1).bits (accepted::tail) saved vista.nodes.size
    nodeCount counterEmpty scratch
  let prepared := Function.update saved 4 (List.replicate vista.nodes.size true)
  obtain ⟨bodyTime,bodyBound,b⟩ := levelLoop_all vista weights valid length round accepted tail prepared
    (by simp [prepared,table]) (by simp [prepared,indexEmpty]) (by simp [prepared,query])
    (by simp [prepared,flag]) (by simp [prepared])
  let completed := Function.update (Function.update prepared 1 (List.replicate vista.nodes.size true)) 4 []
  obtain ⟨finishTime,finishBound,c⟩ := finishLevel_executes source encoded
    ((accepted && Executable.auditBalanceLevel vista weights round)::tail) completed round vista.nodes.size
    (by simp [completed]) (by simp [completed,prepared,query]) (by simp [completed,prepared,scratch])
  have result : Function.update (Function.update completed 1 []) 2 (round+1).bits=
      Function.update saved 2 (round+1).bits := by
    funext i
    fin_cases i <;> simp [completed,prepared,indexEmpty,counterEmpty]
  rw [result] at c
  refine ⟨_,?_,a.sequence (b.sequence c)⟩
  dsimp only [roundBudget]
  omega

end Counting.StackMachine.AuditBalance
