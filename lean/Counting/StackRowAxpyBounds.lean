import Counting.StackRowAxpy
import Counting.StackRowScaleInput

namespace Counting.StackMachine.RowAxpy
open Routine

theorem scaled_row_length_le (factor : Rat) (row : List Rat) :
    (Encoding.rationalRow.encode (row.map (factor*·))).length ≤
      (RowScale.inputCodec.encode (factor,row)).length+
      3000000000*((RowScale.inputCodec.encode (factor,row)).length+1)^4 := by
  obtain ⟨time,finish,bounded,⟨ran,_⟩,stored⟩ := RowScale.complete_halts factor row
  have dataBound := run_dataLength (initial RowScale.complete.program (RowScale.inputCodec.encode (factor,row))) finish time ran
  rw [initial_dataLength] at dataBound
  have entry := Finset.single_le_sum (f := fun register => (finish.store register).length)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ (1 : Register RowScale.complete.program))
  change (finish.store 1).length ≤ finish.dataLength at entry
  rw [stored] at entry
  omega

def costConstant : Nat := 2000000000*(300000000002)^4

/-- Polynomial bit-operation bound for the composed, actual row operation.
The exponent includes the verified growth bound on the intermediate row. -/
theorem axpy_executes_polynomial (factor : Rat) (pairs : List (Rat×Rat)) :
    ∃ time ≤ costConstant*((Encoding.rational.encode factor).length+
      (Encoding.rationalRow.encode (pairs.map Prod.fst)).length+
      (Encoding.rationalRow.encode (pairs.map Prod.snd)).length+1)^16,
      Executes axpyRoutine (file (Encoding.rational.encode factor)
        (Encoding.rationalRow.encode (pairs.map Prod.fst)) (Encoding.rationalRow.encode (pairs.map Prod.snd)) []) time
        (file (Encoding.rational.encode factor) [] []
          (Encoding.rationalRow.encode (pairs.map (fun pair => pair.1+factor*pair.2)))) := by
  let F := (Encoding.rational.encode factor).length
  let L := (Encoding.rationalRow.encode (pairs.map Prod.fst)).length
  let R := (Encoding.rationalRow.encode (pairs.map Prod.snd)).length
  let S := (Encoding.rationalRow.encode (pairs.map (fun pair => factor*pair.2))).length
  let total := F+L+R
  obtain ⟨time,bounded,ran⟩ := axpy_executes factor pairs
  refine ⟨time,?_,ran⟩
  have intermediate := scaled_row_length_le factor (pairs.map Prod.snd)
  simp only [List.map_map,Function.comp_def] at intermediate
  have inputSize : (RowScale.inputCodec.encode (factor,pairs.map Prod.snd)).length = 2*F+1+R := by
    change (Encoding.frame (Encoding.rational.encode factor)++Encoding.rationalRow.encode (pairs.map Prod.snd)).length = _
    rw [List.length_append,Encoding.frame_length]
  rw [inputSize] at intermediate
  change S ≤ 2*F+1+R+3000000000*(2*F+1+R+1)^4 at intermediate
  have inputPower := Nat.pow_le_pow_left (show 2*F+1+R+1 ≤ 3*(total+1) by omega) 4
  have linear4 : total+1 ≤ (total+1)^4 := Nat.le_self_pow (by decide) _
  rw [show (3*(total+1))^4 = 81*(total+1)^4 by rw [Nat.mul_pow]] at inputPower
  have scaledBound : S ≤ 300000000000*(total+1)^4 := by omega
  have addBase : L+S+1 ≤ 300000000002*(total+1)^4 := by omega
  have addPower := Nat.pow_le_pow_left addBase 4
  have scalePower := Nat.pow_le_pow_left (show F+R+1≤total+1 by omega) 4
  have higher : (total+1)^4 ≤ (total+1)^16 := by
    exact Nat.pow_le_pow_right (by omega) (by decide : 4≤16)
  have addExpanded : (300000000002*(total+1)^4)^4 = (300000000002)^4*(total+1)^16 := by
    rw [Nat.mul_pow,← Nat.pow_mul]
  rw [addExpanded] at addPower
  change time ≤ 300000000*(F+R+1)^4+6*S+6+1000000000*(L+S+1)^4 at bounded
  change time ≤ costConstant*(total+1)^16
  unfold costConstant
  have positive := Nat.one_le_pow' 16 total
  omega

end Counting.StackMachine.RowAxpy
