import Counting.StackFrameReplace
import Counting.EncodingNetwork

namespace Counting.StackMachine.FieldAccess

/-- Direct correspondence with the actual explicit array codec. The unary
field index is one larger than the array index because of the length header. -/
theorem replaceFieldWord_naturalArray (values : Array Nat) (index replacement : Nat)
    (valid : index<values.size) :
    replaceFieldWord ((Encoding.array Encoding.natural).encode values) (index+1)
      (Encoding.natural.encode replacement)=
      (Encoding.array Encoding.natural).encode (values.setIfInBounds index replacement) := by
  simpa only [Encoding.array,Encoding.transport,Array.toList_setIfInBounds] using
    replaceFieldWord_naturalList values.toList index replacement (by simpa using valid)

end Counting.StackMachine.FieldAccess
