import Counting.StackAuditBalanceBody
import Counting.StackAuditBalanceSelect

namespace Counting.StackMachine.AuditBalance
open Routine RealizabilityCheck EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000

abbrev chooseCurrent : Routine 48 := sequence selectCurrent (branchRoutine 45 checkCurrent (skip 48))

def selectedCheck (vista : Executable.Vista) (weights : Array Nat) (round index : Nat) : Bool :=
  if (vista.node index).level=round then Executable.auditBalanceAt vista weights round index else true

theorem chooseCurrent_executes (vista : Executable.Vista) (weights : Array Nat)
    (valid : vista.valid=true) (length : weights.size=vista.nodes.size)
    (round index : Nat) (inside : index<vista.nodes.size)
    (accepted : Bool) (tail : List Bool) (saved : Fin 8 → List Bool)
    (table : saved 0=Encoding.sequence Encoding.node vista.nodes.toList++Encoding.natural.encode vista.bottom)
    (counter : saved 1=List.replicate index true) (query : saved 2=round.bits) (flag : saved 3=[]) :
    ∃ time ≤ 100020000*((Encoding.vista.encode vista).length+
        ((Encoding.array Encoding.natural).encode weights).length+round.size+(round+1).size+index+2)^15,
      Executes chooseCurrent
        (bankFile (Encoding.vista.encode vista) ((Encoding.array Encoding.natural).encode weights)
          (round+1).bits [] (accepted::tail) saved) time
        (bankFile (Encoding.vista.encode vista) ((Encoding.array Encoding.natural).encode weights)
          (round+1).bits [] ((accepted && selectedCheck vista weights round index)::tail) saved) := by
  let source := Encoding.vista.encode vista
  let encoded := (Encoding.array Encoding.natural).encode weights
  let store := bankFile source encoded (round+1).bits [] (accepted::tail) saved
  obtain ⟨selectTime,selectBound,a⟩ := selectCurrent_executes vista weights round index inside accepted tail
    saved table counter query flag
  let decided := Function.update store 45 [decide ((vista.node index).level=round)]
  have flagEmpty : store 45=[] := by simp [store,bankFile,flag]
  have restored : Function.update decided 45 []=store := by
    simp only [decided,Function.update_idem]
    rw [←flagEmpty,Function.update_eq_self]
  let S := source.length+encoded.length+round.size+(round+1).size+index+2
  have positive : 1 ≤ S := by dsimp only [S];omega
  have one : 1 ≤ S^15 := Nat.one_le_pow _ _ positive
  have tableBound : (saved 0).length ≤ source.length := by
    rw [table]
    change _ ≤ (Encoding.natural.encode vista.nodes.size++
      Encoding.sequence Encoding.node vista.nodes.toList++Encoding.natural.encode vista.bottom).length
    simp only [List.length_append]
    omega
  have selectionLimit : selectTime ≤ 8000*S^15 := selectBound.trans
    (Nat.mul_le_mul_left 8000 ((Nat.pow_le_pow_left (by dsimp only [S];omega) 4).trans
      (Nat.pow_le_pow_right positive (by decide))))
  by_cases selected : (vista.node index).level=round
  · obtain ⟨bodyTime,bodyBound,b⟩ := checkCurrent_executes vista weights valid length round index accepted tail saved counter
    have branch := branch_executes_true (45:Fin 50) checkCurrent (skip 48) decided _ [] bodyTime
      (by simp [decided,selected]) (by rw [restored];exact b)
    have combined := a.sequence branch
    simp only [selectedCheck,if_pos selected]
    refine ⟨_,?_,combined⟩
    have bodyLimit : bodyTime ≤ 100001000*S^15 := bodyBound.trans
      (Nat.mul_le_mul_left 100001000 (Nat.pow_le_pow_left (by dsimp only [S,source,encoded];omega) 15))
    change _ ≤ 100020000*S^15
    omega
  · have branch := branch_executes_false (45:Fin 50) checkCurrent (skip 48) decided store [] 0
      (by simp [decided,selected]) (by rw [restored];exact skip_executes store)
    have combined := a.sequence branch
    simp only [selectedCheck,if_neg selected,Bool.and_true]
    refine ⟨_,?_,combined⟩
    change _ ≤ 100020000*S^15
    omega

end Counting.StackMachine.AuditBalance
