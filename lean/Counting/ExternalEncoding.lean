import Counting.ExternalReductionChain
import Counting.EncodingBinary

namespace Counting.External

/-- The variable universe is represented by an explicit table, including
unused variables. Thus its size is bounded by the input word length. -/
abbrev CNFInput := Σ n : ℕ, CNF n

namespace CNFEncoding

abbrev Raw := List Bool × List (List (ℕ × Bool))

def rawCodec : Encoding.Codec Raw :=
  Encoding.product (Encoding.list Encoding.boolean)
    (Encoding.list (Encoding.list (Encoding.product Encoding.natural Encoding.boolean)))

def literalRaw {n : ℕ} (literal : Literal n) : ℕ × Bool :=
  (literal.var.val, literal.positive)

def literalFromRaw (n : ℕ) (literal : ℕ × Bool) : Option (Literal n) :=
  if bounded : literal.1 < n then some ⟨⟨literal.1, bounded⟩, literal.2⟩ else none

def toRaw (input : CNFInput) : Raw :=
  (List.replicate input.1 true, input.2.map (List.map literalRaw))

/-- This total prefix decoder is canonicalized by `Codec.decodeExact`.
The exact decoder rejects non-true table markers and out-of-range variables,
because re-encoding the result must reproduce the entire original word. -/
def fromRaw (input : Raw) : CNFInput :=
  ⟨input.1.length, input.2.map (List.filterMap (literalFromRaw input.1.length))⟩

@[simp] theorem literalFromRaw_literalRaw {n : ℕ} (literal : Literal n) :
    literalFromRaw n (literalRaw literal) = some literal := by
  cases literal
  simp [literalFromRaw, literalRaw]

@[simp] theorem clause_roundtrip {n : ℕ} (clause : List (Literal n)) :
    (clause.map literalRaw).filterMap (literalFromRaw n) = clause := by
  induction clause with
  | nil => rfl
  | cons literal rest ih => simp only [List.map_cons, List.filterMap_cons,
      literalFromRaw_literalRaw, ih]

@[simp] theorem fromRaw_toRaw (input : CNFInput) : fromRaw (toRaw input) = input := by
  rcases input with ⟨n, formula⟩
  dsimp only [fromRaw, toRaw]
  generalize tableEq : List.replicate n true = table
  have sizeEq : table.length = n := by rw [← tableEq, List.length_replicate]
  generalize lengthEq : table.length = k at *
  subst k
  subst n
  simp only [List.map_map, Function.comp_def, clause_roundtrip]
  exact congrArg (Sigma.mk table.length) (List.map_id formula)

def codec : Encoding.Codec CNFInput :=
  Encoding.transport rawCodec toRaw fromRaw fromRaw_toRaw

theorem decodeExact_iff (word : List Bool) (input : CNFInput) :
    codec.decodeExact word = some input ↔ codec.encode input = word :=
  codec.decodeExact_iff word input

theorem encode_injective : Function.Injective codec.encode := codec.injective

theorem literal_length {n : ℕ} (literal : Literal n) :
    ((Encoding.product Encoding.natural Encoding.boolean).encode (literalRaw literal)).length =
      2 * literal.var.val.size + 2 := by
  simp [Encoding.product, Encoding.boolean, literalRaw]

theorem clause_length_bound {n : ℕ} (clause : List (Literal n)) :
    clause.length ≤ ((Encoding.list (Encoding.product Encoding.natural Encoding.boolean)).encode
      (clause.map literalRaw)).length := by
  rw [Encoding.list_length]
  suffices clause.length ≤ ((clause.map literalRaw).map
      (fun lit => ((Encoding.product Encoding.natural Encoding.boolean).encode lit).length)).sum by
    omega
  induction clause with
  | nil => simp
  | cons literal rest ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, literal_length]
      omega

theorem clause_length_positive {n : ℕ} (clause : List (Literal n)) :
    1 ≤ ((Encoding.list (Encoding.product Encoding.natural Encoding.boolean)).encode
      (clause.map literalRaw)).length := by
  rw [Encoding.list_length]
  omega

theorem formula_size_bounds {n : ℕ} (formula : CNF n) :
    formula.length ≤ ((Encoding.list (Encoding.list
      (Encoding.product Encoding.natural Encoding.boolean))).encode
      (formula.map (List.map literalRaw))).length ∧
    formula.width ≤ ((Encoding.list (Encoding.list
      (Encoding.product Encoding.natural Encoding.boolean))).encode
      (formula.map (List.map literalRaw))).length := by
  rw [Encoding.list_length]
  suffices formula.length ≤ ((formula.map (List.map literalRaw)).map
      (fun clause => ((Encoding.list (Encoding.product Encoding.natural Encoding.boolean)).encode
        clause).length)).sum ∧
      formula.width ≤ ((formula.map (List.map literalRaw)).map
      (fun clause => ((Encoding.list (Encoding.product Encoding.natural Encoding.boolean)).encode
        clause).length)).sum by omega
  induction formula with
  | nil => simp [CNF.width]
  | cons clause rest ih =>
      have positive := clause_length_positive clause
      have bounded := clause_length_bound clause
      simp only [List.map_cons, List.sum_cons, List.length_cons, CNF.width]
      omega

/-- All three combinatorial input parameters are bounded by the actual
binary input length, including zero variables and empty clauses. -/
theorem input_size_bounds (input : CNFInput) :
    input.1 ≤ (codec.encode input).length ∧
      input.2.length ≤ (codec.encode input).length ∧
      input.2.width ≤ (codec.encode input).length := by
  rcases input with ⟨n, formula⟩
  have formulaBounds := formula_size_bounds formula
  have table : n ≤ ((Encoding.list Encoding.boolean).encode (List.replicate n true)).length := by
    rw [Encoding.list_length]
    simp [Encoding.boolean]
  change n ≤ (rawCodec.encode (toRaw ⟨n, formula⟩)).length ∧
    formula.length ≤ (rawCodec.encode (toRaw ⟨n, formula⟩)).length ∧
    formula.width ≤ (rawCodec.encode (toRaw ⟨n, formula⟩)).length
  have length : (rawCodec.encode (toRaw ⟨n, formula⟩)).length =
      ((Encoding.list Encoding.boolean).encode (List.replicate n true)).length +
      ((Encoding.list (Encoding.list (Encoding.product Encoding.natural Encoding.boolean))).encode
        (formula.map (List.map literalRaw))).length := List.length_append
  rw [length]
  omega

theorem normalizedX3C_size_bounds (input : CNFInput) :
    3 * (2 * ThreeSAT.slotCount input.2.targetVariables input.2.targetClauses + 1 + 1) ≤
        3 * (CNF.matchingSizeBound (codec.encode input).length + 2) ∧
      input.2.toThreeSAT.toThreeDM.toX3C.kept.card + 1 + 1 ≤
        CNF.matchingSizeBound (codec.encode input).length ^ 3 + 2 := by
  obtain ⟨varBound, clauses, occurrences⟩ := input_size_bounds input
  exact input.2.normalizedX3C_size_bounds _ varBound clauses occurrences

theorem decoded_input_size_bounds (word : List Bool) (input : CNFInput)
    (decoded : codec.decodeExact word = some input) :
    input.1 ≤ word.length ∧ input.2.length ≤ word.length ∧ input.2.width ≤ word.length := by
  rw [← (decodeExact_iff word input).mp decoded]
  exact input_size_bounds input

end CNFEncoding

namespace CNFEncodingExamples

def unusedVariables : CNFInput := ⟨3, []⟩

#guard (CNFEncoding.codec.decodeExact (CNFEncoding.codec.encode unusedVariables)).isSome
#guard (CNFEncoding.codec.decodeExact
  (CNFEncoding.rawCodec.encode ([false], []))).isNone
#guard (CNFEncoding.codec.decodeExact
  (CNFEncoding.rawCodec.encode ([], [[(0, true)]]))).isNone
#guard (CNFEncoding.codec.decodeExact
  (CNFEncoding.rawCodec.encode ([true], [[(1, false)]]))).isNone
#guard (CNFEncoding.codec.decodeExact
  (CNFEncoding.rawCodec.encode ([true], [[(0, false)]]))).isSome
#guard (CNFEncoding.codec.decodeExact []).isNone

end CNFEncodingExamples
end Counting.External
