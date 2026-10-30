import Counting.X3CEncodingBounds

namespace Counting.X3CEncoding

def TripleSyntax (q : Nat) (elements : List Nat) : Prop :=
  elements.length = 3 ∧ elements.Nodup ∧ elements.Pairwise (· ≤ ·) ∧
    ∀ element ∈ elements, element < 3*q

def RawSyntax (raw : Raw) : Prop :=
  (∀ marker ∈ raw.1, marker = true) ∧ 3*(raw.1.length/3) = raw.1.length ∧
    ∀ elements ∈ raw.2, TripleSyntax (raw.1.length/3) elements

theorem tripleRaw_syntax {q : Nat} (triple : Triple q) : TripleSyntax q (tripleRaw triple) := by
  refine ⟨tripleRaw_length triple, ?_, ?_, tripleRaw_member_bound triple⟩
  · exact (Finset.sort_nodup triple.val (· ≤ ·)).map Fin.val_injective
  · exact List.pairwise_map.mpr (Finset.pairwise_sort triple.val (· ≤ ·))

@[simp] theorem inputTriples_pack (q : Nat) (triples : List (Triple q)) :
    inputTriples (pack q triples) = triples := by
  change List.ofFn (fun j => triples.get j) = triples
  exact List.ofFn_get triples

@[simp] theorem toRaw_pack (q : Nat) (triples : List (Triple q)) :
    toRaw (pack q triples) = (List.replicate (3*q) true, triples.map tripleRaw) := by
  change (List.replicate (3*q) true, (inputTriples (pack q triples)).map tripleRaw) = _
  rw [inputTriples_pack]
  rfl

theorem toRaw_syntax (input : Input) : RawSyntax (toRaw input) := by
  unfold RawSyntax toRaw
  simp only [List.mem_replicate, and_imp, List.length_replicate,
    Nat.mul_div_cancel_left _ (by decide : 0 < 3)]
  refine ⟨fun _ _ eq => eq, trivial, ?_⟩
  intro elements member
  obtain ⟨triple, _, rfl⟩ := List.mem_map.mp member
  exact tripleRaw_syntax triple

theorem elements_fromRaw_map (q : Nat) (elements : List Nat)
    (bounded : ∀ element ∈ elements, element < 3*q) :
    (elements.filterMap (elementFromRaw q)).map Fin.val = elements := by
  induction elements with
  | nil => rfl
  | cons head tail ih =>
    have first := bounded head List.mem_cons_self
    have rest := ih (fun element member => bounded element (List.mem_cons_of_mem head member))
    simpa only [List.filterMap_cons, elementFromRaw, first, dif_pos, List.map_cons] using
      congrArg (List.cons head) rest

theorem tripleFromRaw_syntax (q : Nat) (elements : List Nat) (syntaxOk : TripleSyntax q elements) :
    ∃ triple, tripleFromRaw q elements = some triple ∧ tripleRaw triple = elements := by
  obtain ⟨length, nodup, ordered, bounded⟩ := syntaxOk
  let converted := elements.filterMap (elementFromRaw q)
  have mapped : converted.map Fin.val = elements := elements_fromRaw_map q elements bounded
  have convertedNodup : converted.Nodup := List.Nodup.of_map Fin.val (mapped ▸ nodup)
  have convertedLength : converted.length = 3 := by
    rw [← List.length_map Fin.val, mapped, length]
  have cardinality : converted.toFinset.card = 3 := by
    rw [List.toFinset_card_of_nodup convertedNodup, convertedLength]
  have valOrdered : (converted.map Fin.val).Pairwise (· ≤ ·) := by
    rw [mapped]
    exact ordered
  have convertedOrdered : converted.Pairwise (· ≤ ·) :=
    (List.pairwise_map (f := Fin.val) (R := fun a b : Nat => a ≤ b)).mp valOrdered
  refine ⟨⟨converted.toFinset, cardinality⟩, ?_, ?_⟩
  · simp only [tripleFromRaw, show (elements.filterMap (elementFromRaw q)).toFinset.card = 3 from cardinality,
      dif_pos]
    rfl
  · change (converted.toFinset.sort (· ≤ ·)).map Fin.val = elements
    rw [(List.toFinset_sort (· ≤ ·) convertedNodup).mpr convertedOrdered, mapped]

theorem triples_fromRaw_map (q : Nat) (rows : List (List Nat))
    (valid : ∀ elements ∈ rows, TripleSyntax q elements) :
    (rows.filterMap (tripleFromRaw q)).map tripleRaw = rows := by
  induction rows with
  | nil => rfl
  | cons head tail ih =>
    obtain ⟨triple, parsed, encoded⟩ := tripleFromRaw_syntax q head (valid head List.mem_cons_self)
    have rest := ih (fun elements member => valid elements (List.mem_cons_of_mem head member))
    simp only [List.filterMap_cons, parsed, List.map_cons, encoded, rest]

theorem toRaw_fromRaw (raw : Raw) (valid : RawSyntax raw) : toRaw (fromRaw raw) = raw := by
  obtain ⟨markers, cardinality, triples⟩ := valid
  rw [fromRaw, toRaw_pack, triples_fromRaw_map _ _ triples, cardinality]
  have table : raw.1 = List.replicate raw.1.length true := List.eq_replicate_of_mem markers
  rw [← table]

theorem decodeExact_raw_iff (raw : Raw) (input : Input) :
    codec.decodeExact (rawCodec.encode raw) = some input ↔ toRaw input = raw := by
  rw [decodeExact_iff]
  exact rawCodec.injective.eq_iff

/-- The implemented exact decoder accepts precisely the explicitly
specified universe and triple syntax. Duplicate triples are unrestricted. -/
theorem decodeExact_raw_isSome_iff (raw : Raw) :
    (codec.decodeExact (rawCodec.encode raw)).isSome = true ↔ RawSyntax raw := by
  constructor
  · intro success
    obtain ⟨input, decoded⟩ := Option.isSome_iff_exists.mp success
    rw [← (decodeExact_raw_iff raw input).mp decoded]
    exact toRaw_syntax input
  · intro valid
    have decoded := (decodeExact_raw_iff raw (fromRaw raw)).mpr (toRaw_fromRaw raw valid)
    simp only [decoded, Option.isSome_some]

theorem malformed_raw_negative (raw : Raw) (invalid : ¬ RawSyntax raw) :
    ¬ BinaryX3C (rawCodec.encode raw) := by
  rintro ⟨input, decoded, _⟩
  apply invalid
  apply (decodeExact_raw_isSome_iff raw).mp
  simp only [decoded, Option.isSome_some]

end Counting.X3CEncoding
