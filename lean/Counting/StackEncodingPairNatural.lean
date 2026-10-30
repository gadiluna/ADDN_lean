import Counting.StackEncodingPairMachine

namespace Counting.StackMachine.EncodingPrograms

/-- The existing natural prefix codec evaluates the two parsed payloads as
little-endian integers. Exact canonical validation is a separate condition. -/
theorem natural_pair_decode (input : List Bool) :
    (Encoding.product Encoding.natural Encoding.natural).decode input =
      ((Encoding.product frameCodec frameCodec).decode input).map
        (fun ((first,second),suffix) => ((Encoding.value first,Encoding.value second),suffix)) := by
  cases first : Encoding.unframe input with
  | none => simp [Encoding.product,Encoding.natural,frameCodec,first]
  | some pair =>
    obtain ⟨payload,rest⟩:=pair
    cases second : Encoding.unframe rest with
    | none => simp [Encoding.product,Encoding.natural,frameCodec,first,second]
    | some pair => obtain ⟨payload2,suffix⟩:=pair; simp [Encoding.product,Encoding.natural,frameCodec,first,second]

theorem natural_pair_isSome (input : List Bool) :
    ((Encoding.product Encoding.natural Encoding.natural).decode input).isSome =
      ((Encoding.product frameCodec frameCodec).decode input).isSome := by
  rw [natural_pair_decode]
  simp only [Option.isSome_map]

theorem pair_naturalPrefix_computesCleanIn :
    Complexity.ComputesCleanIn (Compiler.compile pairRecognitionProgram)
      (fun input => [((Encoding.product Encoding.natural Encoding.natural).decode input).isSome])
      (Complexity.polynomial (20*(13+3+5)^2) 4) := by
  simpa only [natural_pair_isSome] using pair_computesCleanIn

end Counting.StackMachine.EncodingPrograms
