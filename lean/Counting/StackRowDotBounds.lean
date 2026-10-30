import Counting.StackRowDot
import Counting.StackRowScaleBounds

namespace Counting.StackMachine.RowDot
open Routine RowAdd GaussianBits

theorem heights_le_fields (pairs : List (Rat×Rat)) :
    (pairs.map (fun pair => rationalHeight pair.1+rationalHeight pair.2+3)).sum ≤
      (Encoding.sequence (Encoding.framed Encoding.rational) (pairs.map Prod.fst)).length+
      (Encoding.sequence (Encoding.framed Encoding.rational) (pairs.map Prod.snd)).length := by
  induction pairs with
  | nil => simp [Encoding.sequence]
  | cons pair rest ih =>
    have first := rationalHeight_le_encoded pair.1
    have second := rationalHeight_le_encoded pair.2
    have positive := Encoding.rational_field_length_pos pair.1
    simp only [List.map_cons,List.sum_cons,Encoding.sequence,List.length_append,Encoding.framed_length]
    omega

theorem envelope_le_rows (pairs : List (Rat×Rat)) :
    dotEnvelope pairs 0 ≤ (Encoding.rationalRow.encode (pairs.map Prod.fst)).length+
      (Encoding.rationalRow.encode (pairs.map Prod.snd)).length+1 := by
  have fields := heights_le_fields pairs
  dsimp only [dotEnvelope]
  rw [rationalHeight_zero]
  change _ ≤ (Encoding.natural.encode (pairs.map Prod.fst).length++_).length+
    (Encoding.natural.encode (pairs.map Prod.snd).length++_).length+1
  simp only [List.length_append]
  omega

theorem result_length_le_rows (pairs : List (Rat×Rat)) :
    (Encoding.rational.encode ((pairs.map (fun pair => pair.1*pair.2)).sum)).length ≤
      4*((Encoding.rationalRow.encode (pairs.map Prod.fst)).length+
        (Encoding.rationalRow.encode (pairs.map Prod.snd)).length+1)+3 := by
  have height := dotAcc_height pairs 0
  change rationalHeight (dotAcc pairs 0) ≤ dotEnvelope pairs 0 at height
  rw [dotAcc_eq_sum,zero_add] at height
  have envelope := envelope_le_rows pairs
  have encoded := encoded_le_rationalHeight ((pairs.map (fun pair => pair.1*pair.2)).sum)
  omega

/-- The stack cost is polynomial in the actual encoded rows, including
binary headers. The height envelope applies to every accumulated prefix. -/
theorem dot_executes_polynomial (pairs : List (Rat×Rat)) (leftSuffix rightSuffix : List Bool) :
    ∃ time ≤ 10000000000000*((Encoding.rationalRow.encode (pairs.map Prod.fst)).length+
      (Encoding.rationalRow.encode (pairs.map Prod.snd)).length+leftSuffix.length+rightSuffix.length+1)^4,
      Executes dotRoutine
        (file (Encoding.rationalRow.encode (pairs.map Prod.fst)++leftSuffix)
          (Encoding.rationalRow.encode (pairs.map Prod.snd)++rightSuffix) [] [] [] [] [] [] [] [] []) time
        (file leftSuffix rightSuffix (Encoding.rational.encode ((pairs.map (fun pair => pair.1*pair.2)).sum))
          [] [] [] [] [] [] [] []) := by
  let leftSize := (Encoding.rationalRow.encode (pairs.map Prod.fst)).length
  let rightSize := (Encoding.rationalRow.encode (pairs.map Prod.snd)).length
  let total := leftSize+rightSize+leftSuffix.length+rightSuffix.length
  obtain ⟨time,bounded,ran⟩ := dot_executes pairs leftSuffix rightSuffix
  refine ⟨time,?_,ran⟩
  have envelope := envelope_le_rows pairs
  have count := RowScale.fields_count_le (pairs.map Prod.fst)
  simp only [List.length_map] at count
  have rowEq : leftSize = (Encoding.natural.encode pairs.length).length+
      (Encoding.sequence (Encoding.framed Encoding.rational) (pairs.map Prod.fst)).length := by
    change (Encoding.natural.encode (pairs.map Prod.fst).length++_).length = _
    rw [List.length_map,List.length_append]
  have countBound : pairs.length ≤ total+1 := by omega
  have headerBound : (Encoding.natural.encode pairs.length).length ≤ total := by omega
  have bitsBound : pairs.length.bits.length ≤ total := by
    change (Encoding.frame pairs.length.bits).length ≤ total at headerBound
    rw [Encoding.frame_length] at headerBound
    omega
  have loopPower := Nat.pow_le_pow_left (show 8*dotEnvelope pairs 0+10 ≤ 18*(total+1) by
    change dotEnvelope pairs 0 ≤ leftSize+rightSize+1 at envelope
    omega) 3
  have stepBound : stepBudget (dotEnvelope pairs 0) ≤ 5832000000000*(total+1)^3 := by
    dsimp only [stepBudget]
    nlinarith [Nat.mul_le_mul_left 1000000000 loopPower]
  have loopBound := Nat.mul_le_mul countBound
    (show stepBudget (dotEnvelope pairs 0)+2 ≤ 5832000000000*(total+1)^3+2 by omega)
  have inputCube := Nat.pow_le_pow_left (show (Encoding.rationalRow.encode (pairs.map Prod.fst)++leftSuffix).length+1 ≤ total+1 by
    simp only [List.length_append]; change leftSize+leftSuffix.length+1 ≤ _; omega) 3
  have positive := Nat.one_le_pow' 3 total
  have linear : total+1 ≤ (total+1)^3 := by
    have square := Nat.one_le_pow' 2 total
    have product := Nat.mul_le_mul_left (total+1) square
    nlinarith
  change time ≤ 10000000000000*(total+1)^4
  rw [show (total+1)^4=(total+1)^3*(total+1) by ring]
  nlinarith

end Counting.StackMachine.RowDot
