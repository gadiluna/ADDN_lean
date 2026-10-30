import Counting.StackMatrixAxpy
import Counting.StackRowAxpyInput

namespace Counting.StackMachine.MatrixAxpy
set_option backward.isDefEq.respectTransparency false

def sizeBound (factor : Rat) (rows : List (List Rat)) : Nat :=
  2*(Encoding.rational.encode factor).length+3*(Encoding.rationalMatrix.encode rows).length+3

def costConstant : Nat := RowAxpy.costConstant+17*(RowAxpy.completeCost+1)+200

theorem row_result_length_le (factor : Rat) (rows : List (List Rat)) (target source : Fin rows.length)
    (sameLength : rows[target.val].length=rows[source.val].length) :
    (Encoding.rationalRow.encode (List.zipWith (fun a b=>a+factor*b) rows[target.val] rows[source.val])).length ≤
      (RowAxpy.completeCost+1)*(sizeBound factor rows)^16 := by
  let T := rows[target.val]
  let S := rows[source.val]
  let input := RowAxpy.inputCodec.encode (factor,(T,S))
  let result := Encoding.rationalRow.encode (List.zipWith (fun a b=>a+factor*b) T S)
  have mapped : (T.zip S).map (fun pair=>pair.1+factor*pair.2)=List.zipWith (fun a b=>a+factor*b) T S := by
    rw [List.map_zip_eq_zipWith];rfl
  obtain ⟨time,output,bounded,⟨ran,_⟩,stored⟩ := RowAxpy.complete_halts factor (T.zip S)
  have first : (T.zip S).map Prod.fst=T := List.map_fst_zip sameLength.le
  have second : (T.zip S).map Prod.snd=S := List.map_snd_zip sameLength.ge
  simp only [first,second,mapped] at bounded ran stored
  have dataBound := run_dataLength (initial RowAxpy.complete.program input) output time ran
  rw [initial_dataLength] at dataBound
  have resultBound := Finset.single_le_sum (f:=fun r=>(output.store r).length)
    (fun _ _=>Nat.zero_le _) (Finset.mem_univ (1 : Register RowAxpy.complete.program))
  change (output.store 1).length ≤ output.dataLength at resultBound
  rw [stored] at resultBound
  change result.length ≤ output.dataLength at resultBound
  have tBound := Encoding.framedList_member_length_le Encoding.rationalRow rows T (List.getElem_mem target.isLt)
  have sBound := Encoding.framedList_member_length_le Encoding.rationalRow rows S (List.getElem_mem source.isLt)
  change _ ≤ (Encoding.rationalMatrix.encode rows).length at tBound sBound
  have inputLength : input.length=2*(Encoding.rational.encode factor).length+1+
      (2*(Encoding.rationalRow.encode T).length+1)+(Encoding.rationalRow.encode S).length := by
    simp [input,RowAxpy.inputCodec,Encoding.product,Encoding.framed,Encoding.frame_length,Nat.add_assoc]
  have inputBound : input.length+1 ≤ sizeBound factor rows := by dsimp [sizeBound];omega
  have power := Nat.pow_le_pow_left inputBound 16
  have weighted := Nat.mul_le_mul_left RowAxpy.completeCost power
  have linear := Nat.le_self_pow (by decide : 16≠0) (sizeBound factor rows)
  change time ≤ RowAxpy.completeCost*(input.length+1)^16 at bounded
  change result.length ≤ (RowAxpy.completeCost+1)*(sizeBound factor rows)^16
  rw [Nat.add_mul,one_mul]
  omega

theorem result_length_le (factor : Rat) (rows : List (List Rat)) (target source : Fin rows.length)
    (sameLength : rows[target.val].length=rows[source.val].length) :
    (Encoding.rationalMatrix.encode
      (rows.set target.val (List.zipWith (fun a b=>a+factor*b) rows[target.val] rows[source.val]))).length ≤
      (2*RowAxpy.completeCost+3)*(sizeBound factor rows)^16 := by
  have rowBound := row_result_length_le factor rows target source sameLength
  have replaced := Encoding.framedList_set_length_le Encoding.rationalRow rows target.val
    (List.zipWith (fun a b=>a+factor*b) rows[target.val] rows[source.val]) target.isLt
  change (Encoding.rationalMatrix.encode
    (rows.set target.val (List.zipWith (fun a b=>a+factor*b) rows[target.val] rows[source.val]))).length ≤
    (Encoding.rationalMatrix.encode rows).length+
      2*(Encoding.rationalRow.encode (List.zipWith (fun a b=>a+factor*b) rows[target.val] rows[source.val])).length+1 at replaced
  have linear := Nat.le_self_pow (by decide : 16≠0) (sizeBound factor rows)
  have base : (Encoding.rationalMatrix.encode rows).length+1 ≤ sizeBound factor rows := by dsimp [sizeBound];omega
  simp only [Nat.add_mul,Nat.mul_assoc,one_mul] at rowBound ⊢
  omega

theorem axpy_executes_polynomial (factor : Rat) (rows : List (List Rat)) (target source : Fin rows.length)
    (sameLength : rows[target.val].length=rows[source.val].length) :
    ∃ time ≤ costConstant*(sizeBound factor rows)^16,
      Routine.Executes axpyRoutine
        (file (Encoding.rational.encode factor) (Encoding.rationalMatrix.encode rows)
          (List.replicate (target.val+1) true) (List.replicate (source.val+1) true) [] [] [] [] []) time
        (file (Encoding.rational.encode factor) (Encoding.rationalMatrix.encode
          (rows.set target.val (List.zipWith (fun a b=>a+factor*b) rows[target.val] rows[source.val]))) [] [] [] [] [] [] []) := by
  obtain ⟨time,bounded,ran⟩ := axpy_executes factor rows target source sameLength
  have tBound := Encoding.framedList_member_length_le Encoding.rationalRow rows rows[target.val] (List.getElem_mem target.isLt)
  have sBound := Encoding.framedList_member_length_le Encoding.rationalRow rows rows[source.val] (List.getElem_mem source.isLt)
  have count := Encoding.framedList_count_le Encoding.rationalRow rows
  change _ ≤ (Encoding.rationalMatrix.encode rows).length at tBound sBound count
  have outputBound := row_result_length_le factor rows target source sameLength
  have inner : (Encoding.rational.encode factor).length+(Encoding.rationalRow.encode rows[target.val]).length+
      (Encoding.rationalRow.encode rows[source.val]).length+1 ≤ sizeBound factor rows := by dsimp [sizeBound];omega
  have power := Nat.pow_le_pow_left inner 16
  have weighted := Nat.mul_le_mul_left RowAxpy.costConstant power
  have linear := Nat.le_self_pow (by decide : 16≠0) (sizeBound factor rows)
  have base : (Encoding.rationalMatrix.encode rows).length+1 ≤ sizeBound factor rows := by dsimp [sizeBound];omega
  have targetBound := target.isLt
  have sourceBound := source.isLt
  have positive : 1 ≤ (sizeBound factor rows)^16 := by
    apply Nat.one_le_pow;dsimp [sizeBound];omega
  refine ⟨time,?_,ran⟩
  simp only [costConstant,Nat.add_mul,Nat.mul_assoc,one_mul] at outputBound ⊢
  omega

end Counting.StackMachine.MatrixAxpy
