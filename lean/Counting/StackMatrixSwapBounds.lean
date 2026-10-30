import Counting.StackMatrixSwap

namespace Counting.Encoding

theorem framed_sequence_count_le {α : Type} (codec : Codec α) (values : List α) :
    values.length ≤ (sequence (framed codec) values).length := by
  induction values with
  | nil => simp [sequence]
  | cons value rest ih => simp only [sequence,List.length_cons,List.length_append,framed_length];omega

theorem framed_member_length_le {α : Type} (codec : Codec α) (values : List α)
    (value : α) (member : value∈values) :
    (codec.encode value).length ≤ (sequence (framed codec) values).length := by
  induction values with
  | nil => simp at member
  | cons first rest ih =>
      simp only [List.mem_cons] at member
      simp only [sequence,List.length_append,framed_length]
      rcases member with rfl | member
      · omega
      · have bound := ih member;omega

theorem framedList_count_le {α : Type} (codec : Codec α) (values : List α) :
    values.length ≤ ((list (framed codec)).encode values).length := by
  have bound := framed_sequence_count_le codec values
  change _ ≤ (natural.encode values.length++sequence (framed codec) values).length
  rw [List.length_append]
  omega

theorem framedList_member_length_le {α : Type} (codec : Codec α) (values : List α)
    (value : α) (member : value∈values) :
    (codec.encode value).length ≤ ((list (framed codec)).encode values).length := by
  have bound := framed_member_length_le codec values value member
  change _ ≤ (natural.encode values.length++sequence (framed codec) values).length
  rw [List.length_append]
  omega

theorem framedList_set_length_le {α : Type} (codec : Codec α) (values : List α)
    (index : Nat) (replacement : α) (valid : index<values.length) :
    ((list (framed codec)).encode (values.set index replacement)).length ≤
      ((list (framed codec)).encode values).length+2*(codec.encode replacement).length+1 := by
  rw [←StackMachine.FieldAccess.replaceFieldWord_framedList codec values index replacement valid]
  have bound := StackMachine.FieldAccess.replaceFieldWord_length
    ((list (framed codec)).encode values) (index+1) (frame (codec.encode replacement))
  rw [frame_length] at bound
  omega

end Counting.Encoding

namespace Counting.StackMachine.MatrixSwap

theorem swap_executes_linear (rows : List (List Rat)) (first second : Fin rows.length) :
    ∃ time ≤ 100*((Encoding.rationalMatrix.encode rows).length+1),
      Routine.Executes swapRoutine
        (file (Encoding.rationalMatrix.encode rows) (List.replicate (first.val+1) true)
          (List.replicate (second.val+1) true) [] [] []) time
        (file (Encoding.rationalMatrix.encode ((rows.set first.val rows[second.val]).set second.val rows[first.val]))
          [] [] [] [] []) := by
  obtain ⟨time,bounded,ran⟩ := swap_executes rows first second
  have left := Encoding.framedList_member_length_le Encoding.rationalRow rows rows[first.val]
    (List.getElem_mem first.isLt)
  have right := Encoding.framedList_member_length_le Encoding.rationalRow rows rows[second.val]
    (List.getElem_mem second.isLt)
  have count := Encoding.framedList_count_le Encoding.rationalRow rows
  have replaced := Encoding.framedList_set_length_le Encoding.rationalRow rows first.val rows[second.val] first.isLt
  change _ ≤ (Encoding.rationalMatrix.encode rows).length at left right count
  change (Encoding.rationalMatrix.encode (rows.set first.val rows[second.val])).length ≤
    (Encoding.rationalMatrix.encode rows).length+2*(Encoding.rationalRow.encode rows[second.val]).length+1 at replaced
  refine ⟨time,?_,ran⟩
  have firstBound := first.isLt
  have secondBound := second.isLt
  omega

end Counting.StackMachine.MatrixSwap
