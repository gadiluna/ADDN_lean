import Counting.StackAuditBalanceBank

namespace Counting.StackMachine.AuditBalance
open Routine RealizabilityCheck
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

abbrev checkCurrent : Routine 48 := sequence prepareQuery (sequence bankGuard (clear 36))

/-- One selected physical node: form its binary query from the preserved
traversal counter, check the actual two mass sums, and erase the query. -/
theorem checkCurrent_executes (vista : Executable.Vista) (weights : Array Nat)
    (valid : vista.valid=true) (length : weights.size=vista.nodes.size)
    (round index : Nat) (accepted : Bool) (tail : List Bool) (saved : Fin 8 → List Bool)
    (counter : saved 1=List.replicate index true) :
    ∃ time ≤ 100001000*((Encoding.vista.encode vista).length+
        ((Encoding.array Encoding.natural).encode weights).length+(round+1).size+index+2)^15,
      Executes checkCurrent
        (bankFile (Encoding.vista.encode vista) ((Encoding.array Encoding.natural).encode weights)
          (round+1).bits [] (accepted::tail) saved) time
        (bankFile (Encoding.vista.encode vista) ((Encoding.array Encoding.natural).encode weights)
          (round+1).bits [] ((accepted && Executable.auditBalanceAt vista weights round index)::tail) saved) := by
  let source := Encoding.vista.encode vista
  let encoded := (Encoding.array Encoding.natural).encode weights
  let store := bankFile source encoded (round+1).bits [] (accepted::tail) saved
  obtain ⟨prepareTime,prepareBound,a⟩ := prepareQuery_executes store index
    (by simpa [store,bankFile] using counter)
    (by simp [store,bankFile,massFile])
    (by simp [store,bankFile,massFile])
    (by simp [store,bankFile,massFile])
  have prepared : Function.update store 36 index.bits=
      bankFile source encoded (round+1).bits index.bits (accepted::tail) saved := by
    funext r
    fin_cases r <;> simp [store,bankFile,massFile]
  rw [prepared] at a
  obtain ⟨bodyTime,bodyBound,b⟩ := bankGuard_executes vista weights valid length round index accepted tail saved
  let checked := bankFile source encoded (round+1).bits index.bits
    ((accepted && Executable.auditBalanceAt vista weights round index)::tail) saved
  have c := clear_executes (36:Fin 50) checked
  have query : checked 36=index.bits := by simp [checked,bankFile,massFile]
  rw [query,Encoding.bits_length] at c
  have result : Function.update checked 36 []=
      bankFile source encoded (round+1).bits []
        ((accepted && Executable.auditBalanceAt vista weights round index)::tail) saved := by
    funext r
    fin_cases r <;> simp [checked,bankFile,massFile]
  rw [result] at c
  let S := source.length+encoded.length+(round+1).size+index+2
  have bits : index.size ≤ index := Nat.size_le.mpr Nat.lt_two_pow_self
  have bodyBase : source.length+encoded.length+(round+1).size+index.size+2 ≤ S := by dsimp only [S];omega
  have bodyLimit := bodyBound.trans (Nat.mul_le_mul_left 100000200 (Nat.pow_le_pow_left bodyBase 15))
  have positive : 1 ≤ S := by dsimp only [S];omega
  have square : (index+1)^2 ≤ S^15 :=
    (Nat.pow_le_pow_left (by dsimp only [S];omega : index+1 ≤ S) 2).trans
      (Nat.pow_le_pow_right positive (by decide))
  have linear : S ≤ S^15 := Nat.le_self_pow (by decide) _
  have indexSize : index ≤ S := by dsimp only [S];omega
  have one : 1 ≤ S^15 := Nat.one_le_pow _ _ positive
  refine ⟨_,?_,a.sequence (b.sequence c)⟩
  change _ ≤ 100001000*S^15
  omega

end Counting.StackMachine.AuditBalance
