import Counting.StackEncodingListMachine
import Counting.EncodingNetwork

namespace Counting.StackMachine.EncodingPrograms

/-- Arrays and lists use the same explicit length header and item fields. -/
theorem natural_array_list_exact (input : List Bool) :
    ((Encoding.array Encoding.natural).decodeExact input).isSome=
      ((Encoding.list Encoding.natural).decodeExact input).isSome := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro accepted
    obtain ⟨values,decoded⟩:=Option.isSome_iff_exists.mp accepted
    have encoded := (Encoding.Codec.decodeExact_iff _ input values).mp decoded
    apply Option.isSome_iff_exists.mpr
    refine ⟨values.toList,(Encoding.Codec.decodeExact_iff _ input values.toList).mpr ?_⟩
    exact encoded
  · intro accepted
    obtain ⟨values,decoded⟩:=Option.isSome_iff_exists.mp accepted
    have encoded := (Encoding.Codec.decodeExact_iff _ input values).mp decoded
    apply Option.isSome_iff_exists.mpr
    refine ⟨values.toArray,(Encoding.Codec.decodeExact_iff _ input values.toArray).mpr ?_⟩
    simpa [Encoding.array,Encoding.transport] using encoded

theorem array_computesCleanIn : Complexity.ComputesCleanIn (Compiler.compile listRecognitionProgram)
    (fun input => [((Encoding.array Encoding.natural).decodeExact input).isSome])
    (Complexity.polynomial 75272000 8) := by
  simpa only [natural_array_list_exact] using list_computesCleanIn

end Counting.StackMachine.EncodingPrograms
