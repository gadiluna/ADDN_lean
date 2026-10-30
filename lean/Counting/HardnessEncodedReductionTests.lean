import Counting.HardnessEncodedReduction

namespace Counting.HardnessEncoded.ReductionTests
open Encoding

private def require (label : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError s!"Total reduction test failed: {label}")

private def check (label : String) (source : List Bool) : IO Unit := do
  let network := networkReduce source
  match decodeNetwork? network with
  | none => throw (IO.userError s!"Total reduction test failed: {label} network decode")
  | some target =>
      require s!"{label}: exactly one leader" (inputLeaderCount target == 1)
  match vistaInput.decodeExact (vistaReduce source) with
  | none => throw (IO.userError s!"Total reduction test failed: {label} vista decode")
  | some (view, leaders) =>
      require s!"{label}: valid one-leader vista" (leaders == 1 && view.valid)

private def tests : IO Unit := do
  check "empty malformed word" []
  check "truncated word" [true]
  check "malformed universe" (X3CEncoding.rawCodec.encode ([true], []))
  check "empty satisfiable instance" (X3CEncoding.rawCodec.encode ([], []))
  check "nonempty universe without a cover" (X3CEncoding.rawCodec.encode ([true,true,true], []))
  IO.println "Total binary reduction tests passed (5 source cases, both target encodings)."

#eval tests

example (source : List Bool) (invalid : X3CEncoding.codec.decodeExact source = none) :
    BinarySomeAgentKnows (networkReduce source) ∧ BinaryAtMostOneVista (vistaReduce source) := by
  rw [networkReduce_correct, vistaReduce_correct]
  exact ⟨X3CEncoding.invalid_negative source invalid, X3CEncoding.invalid_negative source invalid⟩

end Counting.HardnessEncoded.ReductionTests
