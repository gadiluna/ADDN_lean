import Counting.StackRowScale

namespace Counting.StackMachine.RowScale
open Routine

theorem product_length_le (factor value : Rat) :
    (Encoding.rational.encode (factor*value)).length ≤
      (Encoding.rational.encode factor).length+(Encoding.rational.encode value).length+
      3000000*((Encoding.rational.encode factor).length+(Encoding.rational.encode value).length+1)^3 := by
  have bounded := computed_length_le RationalArithmetic.Product.completeProduct
    RationalArithmetic.Product.productFunction (Complexity.polynomial 3000000 3)
    RationalArithmetic.Product.product_computes ((Encoding.product Encoding.rational Encoding.rational).encode (factor,value))
  rw [RationalArithmetic.Product.productFunction_rationals] at bounded
  simpa only [Complexity.polynomial,Encoding.product,List.length_append] using bounded

theorem scaled_fields_length_le (factor : Rat) (row : List Rat) (limit : Nat)
    (bounded : ∀ value∈row,(Encoding.rational.encode value).length≤limit) :
    (Encoding.sequence (Encoding.framed Encoding.rational) (row.map (factor*·))).length ≤
      row.length*(2*((Encoding.rational.encode factor).length+limit+
        3000000*((Encoding.rational.encode factor).length+limit+1)^3)+1) := by
  induction row with
  | nil => simp [Encoding.sequence]
  | cons value rest ih =>
    have tail := ih (by intro x member; exact bounded x (List.mem_cons_of_mem value member))
    have current := product_length_le factor value
    have size := bounded value (List.mem_cons_self)
    have power := Nat.pow_le_pow_left (show (Encoding.rational.encode factor).length+(Encoding.rational.encode value).length+1 ≤
      (Encoding.rational.encode factor).length+limit+1 by omega) 3
    simp only [List.map_cons,Encoding.sequence,List.length_append,Encoding.framed_length,List.length_cons]
    nlinarith

theorem member_field_length_le (row : List Rat) (value : Rat) (member : value∈row) :
    (Encoding.rational.encode value).length ≤ (Encoding.sequence (Encoding.framed Encoding.rational) row).length := by
  induction row with
  | nil => simp at member
  | cons head rest ih =>
    simp only [List.mem_cons] at member
    simp only [Encoding.sequence,List.length_append,Encoding.framed_length]
    rcases member with rfl | member
    · omega
    · have tail := ih member
      omega

theorem member_row_length_le (row : List Rat) (value : Rat) (member : value∈row) :
    (Encoding.rational.encode value).length ≤ (Encoding.rationalRow.encode row).length := by
  have bounded := member_field_length_le row value member
  change _ ≤ (Encoding.natural.encode row.length++Encoding.sequence (Encoding.framed Encoding.rational) row).length
  rw [List.length_append]
  omega

theorem scale_executes_polynomial (factor : Rat) (row : List Rat) (suffix : List Bool) :
    ∃ time ≤ 300000000*((Encoding.rational.encode factor).length+(Encoding.rationalRow.encode row).length+suffix.length+1)^4,
      Executes scaleRoutine (file (Encoding.rational.encode factor) (Encoding.rationalRow.encode row++suffix) [] [] [] [] [] [] []) time
        (file (Encoding.rational.encode factor) suffix (Encoding.rationalRow.encode (row.map (factor*·))) [] [] [] [] [] []) := by
  let scalar := (Encoding.rational.encode factor).length
  let rowSize := (Encoding.rationalRow.encode row).length
  let total := scalar+rowSize+suffix.length
  obtain ⟨time,bounded,ran⟩ := scale_executes factor row suffix rowSize (member_row_length_le row)
  refine ⟨time,?_,ran⟩
  have outputs := scaled_fields_length_le factor row rowSize (member_row_length_le row)
  have count := fields_count_le row
  have rowEq : rowSize = (Encoding.natural.encode row.length).length+
      (Encoding.sequence (Encoding.framed Encoding.rational) row).length := List.length_append
  have countBound : row.length ≤ total+1 := by omega
  have headerBound : (Encoding.natural.encode row.length).length ≤ total := by omega
  have cube := Nat.pow_le_pow_left (show scalar+rowSize+1 ≤ total+1 by omega) 3
  have inputCube := Nat.pow_le_pow_left (show (Encoding.rationalRow.encode row++suffix).length+1 ≤ total+1 by
    simp only [List.length_append]; change rowSize+suffix.length+1 ≤ _; omega) 3
  have loopBound := Nat.mul_le_mul countBound
    (show 150000000*(scalar+rowSize+1)^3+2 ≤ 150000000*(total+1)^3+2 by omega)
  have outputBound := Nat.mul_le_mul countBound
    (show 2*(scalar+rowSize+3000000*(scalar+rowSize+1)^3)+1 ≤ 2*(total+3000000*(total+1)^3)+1 by omega)
  change (Encoding.sequence (Encoding.framed Encoding.rational) (row.map (factor*·))).length ≤
    row.length*(2*(scalar+rowSize+3000000*(scalar+rowSize+1)^3)+1) at outputs
  have positive := Nat.one_le_pow' 3 total
  have linear : total+1 ≤ (total+1)^3 := by
    have square := Nat.one_le_pow' 2 total
    have product := Nat.mul_le_mul_left (total+1) square
    nlinarith
  change time ≤ 300000000*(total+1)^4
  change time ≤ 1800*((Encoding.rationalRow.encode row++suffix).length+1)^3+
    row.length*(150000000*(scalar+rowSize+1)^3+2)+
    8*(Encoding.sequence (Encoding.framed Encoding.rational) (row.map (factor*·))).length+
    12*(Encoding.natural.encode row.length).length+17 at bounded
  rw [show (total+1)^4 = (total+1)^3*(total+1) by ring]
  nlinarith

end Counting.StackMachine.RowScale
