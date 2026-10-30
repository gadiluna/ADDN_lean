import Counting.StackAuditBalanceChoice

namespace Counting.StackMachine.AuditBalance
open Routine RealizabilityCheck
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

abbrev balanceItem : Routine 48 := sequence chooseCurrent (pushBit 43 true)

theorem bankFile_saved_update (source weights target query status : List Bool)
    (saved : Fin 8 → List Bool) (index : Fin 8) (word : List Bool) :
    Function.update (bankFile source weights target query status saved)
      ⟨index.val+42,by omega⟩ word=
      bankFile source weights target query status (Function.update saved index word) := by
  funext r
  by_cases inside : r.val<42
  · have different : r≠(⟨index.val+42,by omega⟩ : Fin 50) := by
      intro equal
      have value := congrArg Fin.val equal
      change r.val=index.val+42 at value
      omega
    simp [bankFile,inside,different]
  · by_cases same : r.val=index.val+42
    · have equal : r=(⟨index.val+42,by omega⟩ : Fin 50) := Fin.ext same
      have lower : (⟨r.val-42,by omega⟩ : Fin 8)=index := by
        apply Fin.ext
        change r.val-42=index.val
        omega
      calc
        _=word := by simp [Function.update,equal]
        _=_ := by simp [bankFile,inside,lower]
    · have different : r≠(⟨index.val+42,by omega⟩ : Fin 50) := by
        intro equal
        have value := congrArg Fin.val equal
        change r.val=index.val+42 at value
        exact same value
      have lower : (⟨r.val-42,by omega⟩ : Fin 8)≠index := by
        intro equal
        have value := congrArg Fin.val equal
        change r.val-42=index.val at value
        omega
      simp [bankFile,inside,different,lower]

theorem balanceItem_executes (vista : Executable.Vista) (weights : Array Nat)
    (valid : vista.valid=true) (length : weights.size=vista.nodes.size)
    (round index : Nat) (inside : index<vista.nodes.size)
    (accepted : Bool) (tail : List Bool) (saved : Fin 8 → List Bool)
    (table : saved 0=Encoding.sequence Encoding.node vista.nodes.toList++Encoding.natural.encode vista.bottom)
    (counter : saved 1=List.replicate index true) (query : saved 2=round.bits) (flag : saved 3=[]) :
    ∃ time ≤ 100020100*((Encoding.vista.encode vista).length+
        ((Encoding.array Encoding.natural).encode weights).length+round.size+(round+1).size+index+2)^15,
      Executes balanceItem
        (bankFile (Encoding.vista.encode vista) ((Encoding.array Encoding.natural).encode weights)
          (round+1).bits [] (accepted::tail) saved) time
        (bankFile (Encoding.vista.encode vista) ((Encoding.array Encoding.natural).encode weights)
          (round+1).bits [] ((accepted && selectedCheck vista weights round index)::tail)
          (Function.update saved 1 (List.replicate (index+1) true))) := by
  obtain ⟨time,bounded,a⟩ := chooseCurrent_executes vista weights valid length round index inside accepted tail saved table counter query flag
  let checked := bankFile (Encoding.vista.encode vista) ((Encoding.array Encoding.natural).encode weights)
    (round+1).bits [] ((accepted && selectedCheck vista weights round index)::tail) saved
  have b := pushBit_executes (43:Fin 50) true checked
  have source : checked 43=List.replicate index true := by simpa [checked,bankFile] using counter
  rw [source,←List.replicate_succ] at b
  have result : Function.update checked 43 (List.replicate (index+1) true)=
      bankFile (Encoding.vista.encode vista) ((Encoding.array Encoding.natural).encode weights)
        (round+1).bits [] ((accepted && selectedCheck vista weights round index)::tail)
        (Function.update saved 1 (List.replicate (index+1) true)) :=
    bankFile_saved_update _ _ _ _ _ saved 1 _
  rw [result] at b
  refine ⟨_,?_,a.sequence b⟩
  have one : 1 ≤ ((Encoding.vista.encode vista).length+
      ((Encoding.array Encoding.natural).encode weights).length+round.size+(round+1).size+index+2)^15 :=
    Nat.one_le_pow _ _ (by omega)
  omega

end Counting.StackMachine.AuditBalance
