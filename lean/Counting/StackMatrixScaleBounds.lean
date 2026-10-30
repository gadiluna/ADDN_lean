import Counting.StackMatrixScale
import Counting.StackRowAxpyBounds

namespace Counting.StackMachine.MatrixScale

theorem scaledRow_length_le (factor : Rat) (rows : List (List Rat)) (index : Fin rows.length) :
    (Encoding.rationalRow.encode (rows[index.val].map (factor*·))).length ≤
      3000000001*(2*(Encoding.rational.encode factor).length+(Encoding.rationalMatrix.encode rows).length+2)^4 := by
  have rowBound := Encoding.framedList_member_length_le Encoding.rationalRow rows rows[index.val]
    (List.getElem_mem index.isLt)
  have outputBound := RowAxpy.scaled_row_length_le factor rows[index.val]
  have sourceLength : (RowScale.inputCodec.encode (factor,rows[index.val])).length=
      2*(Encoding.rational.encode factor).length+1+(Encoding.rationalRow.encode rows[index.val]).length := by
    simp [RowScale.inputCodec,Encoding.product,Encoding.framed,Encoding.frame_length]
  change _ ≤ (Encoding.rationalMatrix.encode rows).length at rowBound
  let total := 2*(Encoding.rational.encode factor).length+(Encoding.rationalMatrix.encode rows).length+2
  have sourceBound : (RowScale.inputCodec.encode (factor,rows[index.val])).length+1≤total := by
    dsimp [total];omega
  have power := Nat.pow_le_pow_left sourceBound 4
  have linear : total≤total^4 := Nat.le_self_pow (by decide : 4≠0) total
  change _≤3000000001*total^4
  omega

theorem result_length_le (factor : Rat) (rows : List (List Rat)) (index : Fin rows.length) :
    (Encoding.rationalMatrix.encode (rows.set index.val (rows[index.val].map (factor*·)))).length ≤
      6000000004*(2*(Encoding.rational.encode factor).length+(Encoding.rationalMatrix.encode rows).length+2)^4 := by
  have rowBound := scaledRow_length_le factor rows index
  have replaced := Encoding.framedList_set_length_le Encoding.rationalRow rows index.val
    (rows[index.val].map (factor*·)) index.isLt
  change (Encoding.rationalMatrix.encode (rows.set index.val (rows[index.val].map (factor*·)))).length≤
    (Encoding.rationalMatrix.encode rows).length+2*(Encoding.rationalRow.encode (rows[index.val].map (factor*·))).length+1 at replaced
  let total := 2*(Encoding.rational.encode factor).length+(Encoding.rationalMatrix.encode rows).length+2
  have linear : total≤total^4 := Nat.le_self_pow (by decide : 4≠0) total
  have matrixBound : (Encoding.rationalMatrix.encode rows).length+1≤total := by dsimp [total];omega
  change _≤3000000001*total^4 at rowBound
  change _≤6000000004*total^4
  omega

theorem scale_executes_polynomial (factor : Rat) (rows : List (List Rat)) (index : Fin rows.length) :
    ∃ time ≤ 60000000000*(2*(Encoding.rational.encode factor).length+(Encoding.rationalMatrix.encode rows).length+2)^4,
      Routine.Executes scaleRoutine
        (file (Encoding.rational.encode factor) (Encoding.rationalMatrix.encode rows)
          (List.replicate (index.val+1) true) [] [] []) time
        (file (Encoding.rational.encode factor)
          (Encoding.rationalMatrix.encode (rows.set index.val (rows[index.val].map (factor*·)))) [] [] [] []) := by
  obtain ⟨time,bounded,ran⟩ := scale_executes factor rows index
  have rowBound := Encoding.framedList_member_length_le Encoding.rationalRow rows rows[index.val]
    (List.getElem_mem index.isLt)
  have count := Encoding.framedList_count_le Encoding.rationalRow rows
  change _≤(Encoding.rationalMatrix.encode rows).length at rowBound count
  have outputBound := scaledRow_length_le factor rows index
  let total := 2*(Encoding.rational.encode factor).length+(Encoding.rationalMatrix.encode rows).length+2
  have power := Nat.pow_le_pow_left (show (Encoding.rational.encode factor).length+
    (Encoding.rationalRow.encode rows[index.val]).length+1≤total by dsimp [total];omega) 4
  have linear : total≤total^4 := Nat.le_self_pow (by decide : 4≠0) total
  have matrixBound : (Encoding.rationalMatrix.encode rows).length+2≤total := by dsimp [total];omega
  have indexBound := index.isLt
  change _≤3000000001*total^4 at outputBound
  refine ⟨time,?_,ran⟩
  change time≤60000000000*total^4
  omega

end Counting.StackMachine.MatrixScale
