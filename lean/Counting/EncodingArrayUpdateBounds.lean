import Counting.EncodingNetwork

namespace Counting.Encoding

/-- Replacing one entry changes only one encoded payload; this also holds
for the total out-of-range list update, which leaves the list unchanged. -/
theorem sequence_set_length_le {α : Type} (codec : Codec α) (values : List α)
    (index : Nat) (replacement : α) :
    (sequence codec (values.set index replacement)).length ≤
      (sequence codec values).length+(codec.encode replacement).length := by
  induction values generalizing index with
  | nil=>simp [sequence]
  | cons first rest ih=>
    cases index with
    | zero=>simp only [List.set_cons_zero,sequence,List.length_append];omega
    | succ index=>
      have bound:=ih index
      simp only [List.set_cons_succ,sequence,List.length_append]
      omega

theorem list_set_length_le {α : Type} (codec : Codec α) (values : List α)
    (index : Nat) (replacement : α) :
    ((list codec).encode (values.set index replacement)).length ≤
      ((list codec).encode values).length+(codec.encode replacement).length := by
  have bound:=sequence_set_length_le codec values index replacement
  simp only [list,List.length_set,List.length_append]
  omega

theorem array_setIfInBounds_length_le {α : Type} (codec : Codec α) (values : Array α)
    (index : Nat) (replacement : α) :
    ((array codec).encode (values.setIfInBounds index replacement)).length ≤
      ((array codec).encode values).length+(codec.encode replacement).length := by
  simpa only [array,transport,Array.toList_setIfInBounds] using
    list_set_length_le codec values.toList index replacement

theorem naturalArray_setIfInBounds_length (values : Array Nat) (index replacement : Nat) :
    ((array natural).encode (values.setIfInBounds index replacement)).length ≤
      ((array natural).encode values).length+2*replacement.size+1 := by
  simpa only [natural_length,Nat.add_assoc] using array_setIfInBounds_length_le natural values index replacement

/-- A sequence of updates adds their encoded payload lengths, rather than
multiplying a bound on the whole array at every step. -/
theorem array_updates_length_le {α : Type} (codec : Codec α) (values : Array α)
    (updates : List (Nat×α)) :
    ((array codec).encode (updates.foldl (fun state update=>state.setIfInBounds update.1 update.2) values)).length ≤
      ((array codec).encode values).length+(updates.map (fun update=>(codec.encode update.2).length)).sum := by
  induction updates generalizing values with
  | nil=>simp
  | cons update rest ih=>
    have one:=array_setIfInBounds_length_le codec values update.1 update.2
    have more:=ih (values.setIfInBounds update.1 update.2)
    simp only [List.foldl_cons,List.map_cons,List.sum_cons]
    omega

end Counting.Encoding
