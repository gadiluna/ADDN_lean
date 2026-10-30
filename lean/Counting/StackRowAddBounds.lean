import Counting.StackRowAdd
import Counting.StackRowScaleBounds

namespace Counting.StackMachine.RowAdd
open Routine

theorem sum_length_le (first second : Rat) :
    (Encoding.rational.encode (first+second)).length ≤
      (Encoding.rational.encode first).length+(Encoding.rational.encode second).length+
      14000000*((Encoding.rational.encode first).length+(Encoding.rational.encode second).length+1)^3 := by
  have bounded := computed_length_le RationalArithmetic.Addition.completeAddition
    RationalArithmetic.Addition.additionFunction (Complexity.polynomial 14000000 3)
    RationalArithmetic.Addition.addition_computes ((Encoding.product Encoding.rational Encoding.rational).encode (first,second))
  rw [RationalArithmetic.Addition.additionFunction_rationals] at bounded
  simpa only [Complexity.polynomial,Encoding.product,List.length_append] using bounded

theorem sum_fields_length_le (pairs : List (Rat×Rat)) (limit : Nat)
    (bounded : ∀ pair∈pairs,(Encoding.rational.encode pair.1).length+(Encoding.rational.encode pair.2).length≤limit) :
    (Encoding.sequence (Encoding.framed Encoding.rational) (pairs.map (fun pair => pair.1+pair.2))).length ≤
      pairs.length*(2*(limit+14000000*(limit+1)^3)+1) := by
  induction pairs with
  | nil => simp [Encoding.sequence]
  | cons pair rest ih =>
    have tail := ih (by intro x member; exact bounded x (List.mem_cons_of_mem pair member))
    have current := sum_length_le pair.1 pair.2
    have size := bounded pair (List.mem_cons_self)
    have power := Nat.pow_le_pow_left (show (Encoding.rational.encode pair.1).length+(Encoding.rational.encode pair.2).length+1 ≤ limit+1 by omega) 3
    simp only [List.map_cons,Encoding.sequence,List.length_append,Encoding.framed_length,List.length_cons]
    nlinarith

theorem member_rows_length_le (pairs : List (Rat×Rat)) (pair : Rat×Rat) (member : pair∈pairs) :
    (Encoding.rational.encode pair.1).length+(Encoding.rational.encode pair.2).length ≤
      (Encoding.rationalRow.encode (pairs.map Prod.fst)).length+(Encoding.rationalRow.encode (pairs.map Prod.snd)).length := by
  have left := RowScale.member_row_length_le (pairs.map Prod.fst) pair.1 (List.mem_map_of_mem member)
  have right := RowScale.member_row_length_le (pairs.map Prod.snd) pair.2 (List.mem_map_of_mem member)
  omega

theorem add_executes_polynomial (pairs : List (Rat×Rat)) (leftSuffix rightSuffix : List Bool) :
    ∃ time ≤ 1000000000*((Encoding.rationalRow.encode (pairs.map Prod.fst)).length+
      (Encoding.rationalRow.encode (pairs.map Prod.snd)).length+leftSuffix.length+rightSuffix.length+1)^4,
      Executes addRoutine (file (Encoding.rationalRow.encode (pairs.map Prod.fst)++leftSuffix)
        (Encoding.rationalRow.encode (pairs.map Prod.snd)++rightSuffix) [] [] [] [] [] [] [] [] []) time
        (file leftSuffix rightSuffix (Encoding.rationalRow.encode (pairs.map (fun pair => pair.1+pair.2))) [] [] [] [] [] [] [] []) := by
  let leftSize := (Encoding.rationalRow.encode (pairs.map Prod.fst)).length
  let rightSize := (Encoding.rationalRow.encode (pairs.map Prod.snd)).length
  let total := leftSize+rightSize+leftSuffix.length+rightSuffix.length
  obtain ⟨time,bounded,ran⟩ := add_executes pairs leftSuffix rightSuffix (leftSize+rightSize) (member_rows_length_le pairs)
  refine ⟨time,?_,ran⟩
  have outputs := sum_fields_length_le pairs (leftSize+rightSize) (member_rows_length_le pairs)
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
  have cube := Nat.pow_le_pow_left (show leftSize+rightSize+1 ≤ total+1 by omega) 3
  have inputCube := Nat.pow_le_pow_left (show (Encoding.rationalRow.encode (pairs.map Prod.fst)++leftSuffix).length+1 ≤ total+1 by
    simp only [List.length_append]; change leftSize+leftSuffix.length+1 ≤ _; omega) 3
  have loopBound := Nat.mul_le_mul countBound
    (show 700000000*(leftSize+rightSize+1)^3+2 ≤ 700000000*(total+1)^3+2 by omega)
  have outputBound := Nat.mul_le_mul countBound
    (show 2*(leftSize+rightSize+14000000*(leftSize+rightSize+1)^3)+1 ≤ 2*(total+14000000*(total+1)^3)+1 by omega)
  have positive := Nat.one_le_pow' 3 total
  have linear : total+1 ≤ (total+1)^3 := by
    have square := Nat.one_le_pow' 2 total
    have product := Nat.mul_le_mul_left (total+1) square
    nlinarith
  change time ≤ 1000000000*(total+1)^4
  change time ≤ 1800*((Encoding.rationalRow.encode (pairs.map Prod.fst)++leftSuffix).length+1)^3+
    6*pairs.length.bits.length+pairs.length*(700000000*(leftSize+rightSize+1)^3+2)+
    8*(Encoding.sequence (Encoding.framed Encoding.rational) (pairs.map (fun pair => pair.1+pair.2))).length+
    12*(Encoding.natural.encode pairs.length).length+22 at bounded
  rw [show (total+1)^4 = (total+1)^3*(total+1) by ring]
  nlinarith

end Counting.StackMachine.RowAdd
