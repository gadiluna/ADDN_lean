import Counting.X3CEncodingValidation
import Counting.X3CEncodingCNF

namespace Counting.X3CEncoding.Tests

private def duplicates : Input :=
  ⟨1, 2, ⟨fun _ => Finset.univ, by intro j; decide⟩⟩

private def accepts (raw : Raw) : Bool := (codec.decodeExact (rawCodec.encode raw)).isSome

-- Canonical input, duplicated triples, and an explicitly empty universe.
#guard accepts ([true,true,true], [[0,1,2]])
#guard accepts ([true,true,true], [[0,1,2],[0,1,2]])
#guard accepts ([], [])
#guard ((codec.decodeExact (codec.encode duplicates)).map (fun input => input.2.1)) = some 2

-- Marker, universe cardinality, range, row cardinality, repetition, ordering,
-- truncated data, and trailing data are all rejected.
#guard !accepts ([true,false,true], [[0,1,2]])
#guard !accepts ([true,true], [])
#guard !accepts ([true,true,true], [[0,1,3]])
#guard !accepts ([true,true,true], [[0,1]])
#guard !accepts ([true,true,true], [[0,1,1]])
#guard !accepts ([true,true,true], [[2,1,0]])
#guard (codec.decodeExact []).isNone
#guard (codec.decodeExact (codec.encode duplicates ++ [false])).isNone

example : BinaryX3C (codec.encode duplicates) := by
  apply (encoded_yes_iff duplicates).mpr
  refine ⟨{(0 : Fin 2)}, ?_⟩
  change ∀ element : Fin 3, (({(0 : Fin 2)} : Finset (Fin 2)).filter
    (fun _ => element ∈ (Finset.univ : Finset (Fin 3)))).card = 1
  decide

example : ¬ BinaryX3C (codec.encode CNFReduction.noInstance) := by
  rw [encoded_yes_iff]
  exact CNFReduction.noInstance_negative

example : ¬ BinaryX3C (CNFReduction.reduce []) := by
  rw [CNFReduction.reduce_correct]
  apply CNFReduction.malformed_source_negative
  decide

example : BinaryX3C (CNFReduction.bits ⟨0, []⟩) := by
  rw [CNFReduction.bits_correct]
  exact ⟨Fin.elim0, rfl⟩

example : ¬ BinaryX3C (CNFReduction.bits ⟨0, [[]]⟩) := by
  rw [CNFReduction.bits_correct]
  simp [External.CNF.Satisfiable, External.CNF.eval]

end Counting.X3CEncoding.Tests
