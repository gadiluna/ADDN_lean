import Counting.X3CEncodingBounds
import Counting.ExternalEncoding
import Counting.ComplexityModel

/-! A total executable binary map for the established combinatorial
CNF-to-X3C chain. Correctness and output length are proved separately
from the still-required machine implementation and step bound. -/
namespace Counting.X3CEncoding.CNFReduction
open External

def BinaryCNFSAT : Complexity.Language :=
  Complexity.encodedLanguage CNFEncoding.codec (fun input => input.2.Satisfiable)

def input (source : CNFInput) : Input :=
  ⟨_, _, source.2.toThreeSAT.toThreeDM.toX3C⟩

theorem input_correct (source : CNFInput) :
    (∃ chosen, (input source).2.2.IsExactCover chosen) ↔ source.2.Satisfiable :=
  source.2.toThreeSAT.toThreeDM.toX3C.normalize_exactCover_iff.symm.trans
    source.2.normalizedX3C_yes_iff

def bits (source : CNFInput) : List Bool := codec.encode (input source)

theorem bits_correct (source : CNFInput) : BinaryX3C (bits source) ↔ source.2.Satisfiable :=
  (encoded_yes_iff (input source)).trans (input_correct source)

/-- A nonempty universe with no triples is a fixed valid negative input. -/
def noInstance : Input := ⟨1, 0, ⟨fun j => Fin.elim0 j, fun j => Fin.elim0 j⟩⟩

theorem noInstance_negative : ¬ ∃ chosen, noInstance.2.2.IsExactCover chosen := by
  rintro ⟨chosen, cover⟩
  have zero := cover (0 : Fin 3)
  have empty : chosen = ∅ := Finset.eq_empty_of_forall_notMem (fun element => Fin.elim0 element)
  simp [empty] at zero

def reduce (word : List Bool) : List Bool :=
  match CNFEncoding.codec.decodeExact word with
  | some source => bits source
  | none => codec.encode noInstance

theorem decoded_source_correct (word : List Bool) (source : CNFInput)
    (decoded : CNFEncoding.codec.decodeExact word = some source) :
    word ∈ BinaryCNFSAT ↔ source.2.Satisfiable := by
  rw [← (CNFEncoding.decodeExact_iff word source).mp decoded]
  exact Complexity.encodedLanguage_iff _ _ source

theorem malformed_source_negative (word : List Bool)
    (invalid : CNFEncoding.codec.decodeExact word = none) : word ∉ BinaryCNFSAT := by
  rintro ⟨source, encoded, _⟩
  have decoded := (CNFEncoding.decodeExact_iff word source).mpr encoded
  rw [invalid] at decoded
  contradiction

/-- This is a semantic many-one equivalence on every binary word,
including malformed source codes. It makes no polynomial-time claim. -/
theorem reduce_correct (word : List Bool) : BinaryX3C (reduce word) ↔ word ∈ BinaryCNFSAT := by
  cases decoded : CNFEncoding.codec.decodeExact word with
  | none =>
    simp only [reduce, decoded, encoded_yes_iff, noInstance_negative, false_iff]
    exact malformed_source_negative word decoded
  | some source =>
    simp only [reduce, decoded]
    exact (bits_correct source).trans (decoded_source_correct word source decoded).symm

theorem input_parameters (source : CNFInput) :
    (input source).1 ≤ CNF.matchingSizeBound (CNFEncoding.codec.encode source).length ∧
      (input source).2.1 ≤ (CNF.matchingSizeBound (CNFEncoding.codec.encode source).length)^3 := by
  obtain ⟨vars, clauses, occurrences⟩ := CNFEncoding.input_size_bounds source
  have vertices := source.2.matching_order_bound _ vars clauses occurrences
  have triples := graphToThreeDM_size
    (2*ThreeSAT.slotCount source.2.targetVariables source.2.targetClauses) source.2.toThreeSAT.indexedArc
  exact ⟨vertices, triples.trans (Nat.pow_le_pow_left vertices 3)⟩

def sizeBound (length : Nat) : Nat :=
  30*(CNF.matchingSizeBound length+(CNF.matchingSizeBound length)^3+1)^2

theorem bits_length (source : CNFInput) :
    (bits source).length ≤ sizeBound (CNFEncoding.codec.encode source).length := by
  obtain ⟨universeBound, triples⟩ := input_parameters source
  exact (encode_length_polynomial (input source)).trans
    (Nat.mul_le_mul_left 30 (Nat.pow_le_pow_left (by omega) 2))

theorem reduce_length (word : List Bool) :
    (reduce word).length ≤ sizeBound word.length + (codec.encode noInstance).length := by
  cases decoded : CNFEncoding.codec.decodeExact word with
  | none => simp [reduce, decoded]
  | some source =>
    have size := bits_length source
    rw [(CNFEncoding.decodeExact_iff word source).mp decoded] at size
    simpa only [reduce, decoded] using size.trans (Nat.le_add_right _ _)

end Counting.X3CEncoding.CNFReduction
