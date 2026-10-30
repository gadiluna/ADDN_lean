import Counting.StackFrameMoveMany

namespace Counting.StackMachine.FieldAccess

/-- Replace the indexed framed field with an already encoded replacement.
Beyond the input, the total extension appends the replacement. Its list-set
specification below explicitly requires an in-range index. -/
def replaceFieldWord (input : List Bool) (index : Nat) (replacement : List Bool) : List Bool :=
  frontMany index input++replacement++skipRest (skipMany index input)

theorem replaceFieldWord_length (input : List Bool) (index : Nat) (replacement : List Bool) :
    (replaceFieldWord input index replacement).length ≤ input.length+replacement.length := by
  have partition := congrArg List.length (frontMany_append index input)
  have suffix := skipRest_length (skipMany index input)
  simp only [List.length_append] at partition
  simp only [replaceFieldWord,List.length_append]
  omega

theorem replaceFieldWord_naturals (values : List Nat) (index replacement : Nat)
    (valid : index<values.length) :
    replaceFieldWord (Encoding.sequence Encoding.natural values) index (Encoding.natural.encode replacement)=
      Encoding.sequence Encoding.natural (values.set index replacement) := by
  induction index generalizing values with
  | zero =>
      cases values with
      | nil => simp at valid
      | cons value values => simp [replaceFieldWord,frontMany,skipMany,Encoding.sequence,Encoding.natural,skipRest_frame]
  | succ index ih =>
      cases values with
      | nil => simp at valid
      | cons value values =>
          have inside : index<values.length := by simpa using valid
          have tail := ih values inside
          simp only [replaceFieldWord,frontMany,skipMany,Encoding.sequence,Encoding.natural,
            frameFront_frame,skipRest_frame,List.set_cons_succ,List.append_assoc] at tail ⊢
          rw [tail]

theorem replaceFieldWord_naturalList (values : List Nat) (index replacement : Nat)
    (valid : index<values.length) :
    replaceFieldWord ((Encoding.list Encoding.natural).encode values) (index+1)
      (Encoding.natural.encode replacement)=
      (Encoding.list Encoding.natural).encode (values.set index replacement) := by
  change frontMany (index+1) (Encoding.frame values.length.bits++Encoding.sequence Encoding.natural values)++
    Encoding.natural.encode replacement++skipRest (skipMany (index+1)
      (Encoding.frame values.length.bits++Encoding.sequence Encoding.natural values))=_
  rw [frontMany,frameFront_frame,skipRest_frame,skipMany,skipRest_frame]
  simp only [List.append_assoc]
  have replaced := replaceFieldWord_naturals values index replacement valid
  simp only [replaceFieldWord,List.append_assoc] at replaced
  rw [replaced]
  simp only [Encoding.list,List.length_set,Encoding.natural]

end Counting.StackMachine.FieldAccess
