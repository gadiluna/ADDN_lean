import Counting.X3CDeduplicate
import Counting.EncodingBinary

/-! Canonical binary X3C inputs with an explicitly enumerated universe.
Repeated triples are retained in the raw instance; repeated elements,
out-of-range elements, noncanonical order, and malformed universe tables
are rejected by the exact decoder. -/
namespace Counting.X3CEncoding

abbrev Input := Σ q : Nat, Σ m : Nat, X3C.RawInstance q m
abbrev Triple (q : Nat) := { set : Finset (Fin (3*q)) // set.card = 3 }
abbrev Raw := List Bool × List (List Nat)

def rawCodec : Encoding.Codec Raw :=
  Encoding.product (Encoding.list Encoding.boolean) (Encoding.list (Encoding.list Encoding.natural))

def elementFromRaw (q element : Nat) : Option (Fin (3*q)) :=
  if bounded : element < 3*q then some ⟨element, bounded⟩ else none

def tripleRaw {q : Nat} (triple : Triple q) : List Nat :=
  (triple.val.sort (· ≤ ·)).map Fin.val

def tripleFromRaw (q : Nat) (elements : List Nat) : Option (Triple q) :=
  let set := (elements.filterMap (elementFromRaw q)).toFinset
  if cardinality : set.card = 3 then some ⟨set, cardinality⟩ else none

@[simp] theorem elementFromRaw_val {q : Nat} (element : Fin (3*q)) :
    elementFromRaw q element.val = some element := by
  simp [elementFromRaw, element.isLt]

@[simp] theorem elements_roundtrip {q : Nat} (elements : List (Fin (3*q))) :
    (elements.map Fin.val).filterMap (elementFromRaw q) = elements := by
  induction elements with
  | nil => rfl
  | cons head tail ih => simp only [List.map_cons, List.filterMap_cons, elementFromRaw_val, ih]

@[simp] theorem tripleFromRaw_tripleRaw {q : Nat} (triple : Triple q) :
    tripleFromRaw q (tripleRaw triple) = some triple := by
  simp only [tripleFromRaw, tripleRaw, elements_roundtrip, Finset.sort_toFinset]
  simp only [triple.property, dite_true]

def pack (q : Nat) (triples : List (Triple q)) : Input :=
  ⟨q, triples.length, ⟨fun j => (triples.get j).val, fun j => (triples.get j).property⟩⟩

def inputTriples (input : Input) : List (Triple input.1) :=
  List.ofFn (fun j => ⟨input.2.2.triples j, input.2.2.triple_card j⟩)

theorem pack_inputTriples (input : Input) : pack input.1 (inputTriples input) = input := by
  rcases input with ⟨q, m, inst⟩
  change pack q (List.ofFn (fun j => (⟨inst.triples j, inst.triple_card j⟩ : Triple q))) = _
  generalize listEq : List.ofFn (fun j => (⟨inst.triples j, inst.triple_card j⟩ : Triple q)) = triples
  have sizeEq : triples.length = m := by rw [← listEq, List.length_ofFn]
  generalize lengthEq : triples.length = k at *
  subst k
  subst m
  apply congrArg (Sigma.mk q)
  apply congrArg (Sigma.mk triples.length)
  have functionEq : (fun j => (triples.get j).val) = inst.triples := by
    funext j
    have same := congrArg (fun rows : List (Triple q) => rows[j.val]?) listEq
    simp only [List.getElem?_ofFn, j.isLt, dif_pos, List.getElem?_eq_getElem] at same
    exact congrArg Subtype.val (Option.some.inj same).symm
  cases inst
  cases functionEq
  rfl

def toRaw (input : Input) : Raw :=
  (List.replicate (3*input.1) true, (inputTriples input).map tripleRaw)

/-- The prefix decoder produces a typed candidate on every raw input.
The exact decoder subsequently checks that re-encoding reproduces the
entire input, rejecting every repair made here. -/
def fromRaw (input : Raw) : Input :=
  pack (input.1.length/3) (input.2.filterMap (tripleFromRaw (input.1.length/3)))

@[simp] theorem triples_roundtrip {q : Nat} (triples : List (Triple q)) :
    (triples.map tripleRaw).filterMap (tripleFromRaw q) = triples := by
  induction triples with
  | nil => rfl
  | cons head tail ih => simp only [List.map_cons, List.filterMap_cons, tripleFromRaw_tripleRaw, ih]

@[simp] theorem fromRaw_toRaw (input : Input) : fromRaw (toRaw input) = input := by
  rcases input with ⟨q, m, inst⟩
  dsimp only [fromRaw, toRaw]
  generalize tableEq : List.replicate (3*q) true = table
  have quotient : table.length/3 = q := by
    rw [← tableEq, List.length_replicate, Nat.mul_div_cancel_left _ (by decide : 0 < 3)]
  generalize quotientEq : table.length/3 = k at *
  subst k
  subst q
  rw [triples_roundtrip]
  exact pack_inputTriples ⟨table.length/3, m, inst⟩

def codec : Encoding.Codec Input := Encoding.transport rawCodec toRaw fromRaw fromRaw_toRaw

theorem decodeExact_iff (word : List Bool) (input : Input) :
    codec.decodeExact word = some input ↔ codec.encode input = word := codec.decodeExact_iff word input

theorem encode_injective : Function.Injective codec.encode := codec.injective

@[simp] theorem inputTriples_length (input : Input) : (inputTriples input).length = input.2.1 :=
  List.length_ofFn

@[simp] theorem tripleRaw_length {q : Nat} (triple : Triple q) : (tripleRaw triple).length = 3 := by
  simp only [tripleRaw, List.length_map, Finset.length_sort, triple.property]

theorem triple_encoding_positive {q : Nat} (triple : Triple q) :
    1 ≤ ((Encoding.list Encoding.natural).encode (tripleRaw triple)).length := by
  rw [Encoding.list_length]
  omega

theorem triples_count_bound {q : Nat} (triples : List (Triple q)) :
    triples.length ≤ ((Encoding.list (Encoding.list Encoding.natural)).encode
      (triples.map tripleRaw)).length := by
  rw [Encoding.list_length]
  suffices triples.length ≤ ((triples.map tripleRaw).map
      (fun row => ((Encoding.list Encoding.natural).encode row).length)).sum by omega
  induction triples with
  | nil => simp
  | cons head tail ih =>
    have positive := triple_encoding_positive head
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    omega

/-- Both the universe parameter and the number of triples are controlled
by the actual word length, including unused universe elements. -/
theorem input_size_bounds (input : Input) :
    3*input.1 ≤ (codec.encode input).length ∧ input.2.1 ≤ (codec.encode input).length := by
  have triples := triples_count_bound (inputTriples input)
  rw [inputTriples_length] at triples
  have table : 3*input.1 ≤ ((Encoding.list Encoding.boolean).encode
      (List.replicate (3*input.1) true)).length := by
    rw [Encoding.list_length]
    simp [Encoding.boolean]
  change 3*input.1 ≤ (rawCodec.encode (toRaw input)).length ∧
    input.2.1 ≤ (rawCodec.encode (toRaw input)).length
  have length : (rawCodec.encode (toRaw input)).length =
      ((Encoding.list Encoding.boolean).encode (List.replicate (3*input.1) true)).length +
      ((Encoding.list (Encoding.list Encoding.natural)).encode
        ((inputTriples input).map tripleRaw)).length := List.length_append
  rw [length]
  omega

theorem decoded_input_size_bounds (word : List Bool) (input : Input)
    (decoded : codec.decodeExact word = some input) :
    input.1 ≤ word.length ∧ input.2.1 ≤ word.length := by
  rw [← (decodeExact_iff word input).mp decoded]
  have bounded := input_size_bounds input
  omega

def BinaryX3C (word : List Bool) : Prop :=
  ∃ input, codec.decodeExact word = some input ∧ ∃ chosen, input.2.2.IsExactCover chosen

theorem encoded_yes_iff (input : Input) : BinaryX3C (codec.encode input) ↔
    ∃ chosen, input.2.2.IsExactCover chosen := by
  unfold BinaryX3C
  constructor
  · rintro ⟨other, parsed, cover⟩
    have same := encode_injective ((decodeExact_iff _ _).mp parsed)
    exact same ▸ cover
  · intro cover
    exact ⟨input, (decodeExact_iff _ _).mpr rfl, cover⟩

theorem invalid_negative (word : List Bool) (invalid : codec.decodeExact word = none) :
    ¬ BinaryX3C word := by
  rintro ⟨input, decoded, _⟩
  rw [invalid] at decoded
  contradiction

end Counting.X3CEncoding
