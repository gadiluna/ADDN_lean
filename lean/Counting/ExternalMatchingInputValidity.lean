import Counting.ExternalMatchingParser

namespace Counting.External.MatchingInputValidation
open ThreeDMEncoding

/-- Exact row width is checked in addition to index ranges: the transport
decoder's filterMap must never turn an invalid row into an accepted triple. -/
def validRaw (raw : Raw) : Bool :=
  raw.1.all id && raw.2.all (fun row=>row.length==3 && row.all (fun value=>decide (value < raw.1.length)))

theorem tripleFromRaw_valid (q : Nat) (row : List Nat) (width : row.length=3)
    (bounded : ∀ value∈row,value < q) :
    ∃ triple : Triple q,tripleFromRaw q row=some triple ∧ tripleRaw triple=row := by
  cases row with
  | nil => simp at width
  | cons a rest =>
    cases rest with
    | nil => simp at width
    | cons b rest =>
      cases rest with
      | nil => simp at width
      | cons c rest =>
        have empty : rest=[]:=List.length_eq_zero_iff.mp (by simpa using width)
        subst rest
        let triple : Triple q:=![⟨a,bounded a (by simp)⟩,⟨b,bounded b (by simp)⟩,⟨c,bounded c (by simp)⟩]
        have raw : tripleRaw triple=[a,b,c]:=rfl
        exact ⟨triple,raw ▸ triple_roundtrip triple,raw⟩

theorem rows_reencode (q : Nat) (rows : List (List Nat))
    (valid : ∀ row∈rows,row.length=3 ∧ ∀ value∈row,value < q) :
    (rows.filterMap (tripleFromRaw q)).map tripleRaw=rows := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
    obtain ⟨width,bounded⟩:=valid row (by simp)
    obtain ⟨triple,decoded,encoded⟩:=tripleFromRaw_valid q row width bounded
    rw [List.filterMap_cons,decoded,List.map_cons,encoded,ih]
    intro row member
    exact valid row (by simp [member])

theorem inputTriples_pack (q : Nat) (triples : List (Triple q)) :
    inputTriples (pack q triples)=triples := by
  simp [inputTriples,pack]

theorem validRaw_reencode (raw : Raw) (valid : validRaw raw=true) : toRaw (fromRaw raw)=raw := by
  have checks : raw.1.all id=true ∧
      ∀ row∈raw.2,row.length=3 ∧ ∀ value∈row,value < raw.1.length := by
    simpa only [validRaw,Bool.and_eq_true,List.all_eq_true,beq_iff_eq,decide_eq_true_eq] using valid
  have markers : List.replicate raw.1.length true=raw.1 := by
    apply Eq.symm
    apply List.eq_replicate_length.mpr
    simpa only [List.all_eq_true,id_eq] using checks.1
  apply Prod.ext
  · exact markers
  · change (inputTriples (pack raw.1.length (raw.2.filterMap (tripleFromRaw raw.1.length)))).map tripleRaw=raw.2
    rw [inputTriples_pack]
    exact rows_reencode raw.1.length raw.2 checks.2

@[simp] theorem validRaw_toRaw (input : Input) : validRaw (toRaw input)=true := by
  simp [validRaw,toRaw,tripleRaw]

def validInput (input : List Bool) : Bool :=
  match rawCodec.decodeExact input with
  | none=>false
  | some raw=>validRaw raw

theorem validInput_iff (input : List Bool) : validInput input=true ↔
    ∃ matching : Input,codec.encode matching=input := by
  constructor
  · intro valid
    cases decoded : rawCodec.decodeExact input with
    | none => simp [validInput,decoded] at valid
    | some raw =>
      have checked : validRaw raw=true := by simpa only [validInput,decoded] using valid
      refine ⟨fromRaw raw,?_⟩
      change rawCodec.encode (toRaw (fromRaw raw))=input
      rw [validRaw_reencode raw checked]
      exact (rawCodec.decodeExact_iff input raw).mp decoded
  · rintro ⟨matching,encoded⟩
    have decoded : rawCodec.decodeExact input=some (toRaw matching) :=
      (rawCodec.decodeExact_iff input (toRaw matching)).mpr encoded
    simp only [validInput,decoded,validRaw_toRaw]

theorem validInput_grammar (input : List Bool) (valid : validInput input=true) :
    MatchingVerification.rawParser.exactEffect input=true := by
  obtain ⟨matching,encoded⟩:= (validInput_iff input).mp valid
  rw [←encoded]
  exact MatchingVerification.exactEffect_encoded matching

end Counting.External.MatchingInputValidation
