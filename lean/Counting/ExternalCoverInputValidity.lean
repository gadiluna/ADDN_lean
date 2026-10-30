import Counting.ExternalMatchingInputValidation
import Counting.X3CEncodingValidation

namespace Counting.External.CoverInputValidation
open MatchingVerification

/-- The canonical order of a three-element set, expressed on the exact-width
raw parser's coordinates. Duplicate triples remain permitted. -/
def rowOrdered (row : RawClause) : Bool :=
  decide (row.2.1 < row.2.2.1 ∧ row.2.2.1 < row.2.2.2)

def extraStatus (raw : MatchingVerification.Raw) : Bool :=
  decide (raw.1.length % 3=0) && raw.2.all rowOrdered

def rawStatus (raw : MatchingVerification.Raw) : Bool :=
  MatchingInputValidation.rawStatus raw && extraStatus raw

theorem triple_syntax_iff (q a b c : Nat) :
    X3CEncoding.TripleSyntax q [a,b,c] ↔ a < b ∧ b < c ∧ c < 3*q := by
  simp [X3CEncoding.TripleSyntax,List.pairwise_cons]
  omega

theorem rawStatus_iff (raw : MatchingVerification.Raw) :
    rawStatus raw=true ↔ X3CEncoding.RawSyntax (MatchingVerification.toRaw raw) := by
  simp only [rawStatus,MatchingInputValidation.rawStatus,MatchingInputValidation.rowsRange,
    extraStatus,Bool.and_eq_true,List.all_eq_true,decide_eq_true_eq,
    X3CEncoding.RawSyntax,MatchingVerification.toRaw,List.forall_mem_map]
  constructor
  · rintro ⟨⟨markers,bounded⟩,divisible,ordered⟩
    have size : 3*(raw.1.length/3)=raw.1.length := by omega
    refine ⟨markers,size,?_⟩
    intro row member
    rcases row with ⟨⟨⟩,a,b,c⟩
    have ranges:=bounded ((),a,b,c) member
    have order:=ordered ((),a,b,c) member
    simp only [MatchingInputValidation.rowRange,clauseToRaw,List.all_cons,List.all_nil,
      Bool.and_eq_true,decide_eq_true_eq,List.length_replicate,and_true] at ranges
    simp only [rowOrdered,decide_eq_true_eq] at order
    change a < raw.1.length ∧ b < raw.1.length ∧ c < raw.1.length at ranges
    change a < b ∧ b < c at order
    change X3CEncoding.TripleSyntax (raw.1.length/3) [a,b,c]
    apply (triple_syntax_iff _ a b c).mpr
    exact ⟨order.1,order.2,by omega⟩
  · rintro ⟨markers,size,triples⟩
    refine ⟨⟨markers,?_⟩,by omega,?_⟩
    · intro row member
      rcases row with ⟨⟨⟩,a,b,c⟩
      have triple:=(triple_syntax_iff _ _ _ _).mp (triples ((),a,b,c) member)
      simp only [MatchingInputValidation.rowRange,clauseToRaw,List.all_cons,List.all_nil,
        Bool.and_eq_true,decide_eq_true_eq,List.length_replicate,and_true]
      change a < raw.1.length ∧ b < raw.1.length ∧ c < raw.1.length
      change a < b ∧ b < c ∧ c < 3*(raw.1.length/3) at triple
      omega
    · intro row member
      rcases row with ⟨⟨⟩,a,b,c⟩
      have triple:=(triple_syntax_iff _ _ _ _).mp (triples ((),a,b,c) member)
      simp only [rowOrdered,decide_eq_true_eq]
      exact ⟨triple.1,triple.2.1⟩

def validInput (input : List Bool) : Bool :=
  match MatchingVerification.rawCodec.decodeExact input with
  | none=>false
  | some raw=>rawStatus raw

theorem validInput_sound (input : List Bool) (valid : validInput input=true) :
    ∃ cover : X3CEncoding.Input,X3CEncoding.codec.encode cover=input := by
  cases decoded : MatchingVerification.rawCodec.decodeExact input with
  | none => simp [validInput,decoded] at valid
  | some raw =>
    have checked : rawStatus raw=true := by simpa only [validInput,decoded] using valid
    have syntaxOk:=(rawStatus_iff raw).mp checked
    refine ⟨X3CEncoding.fromRaw (MatchingVerification.toRaw raw),?_⟩
    change X3CEncoding.rawCodec.encode (X3CEncoding.toRaw (X3CEncoding.fromRaw _))=input
    rw [X3CEncoding.toRaw_fromRaw _ syntaxOk]
    exact (MatchingVerification.rawCodec_encode raw).symm.trans
      ((MatchingVerification.rawCodec.decodeExact_iff input raw).mp decoded)

theorem matching_validRaw (cover : X3CEncoding.Input) :
    MatchingInputValidation.validRaw (X3CEncoding.toRaw cover)=true := by
  have syntaxOk:=X3CEncoding.toRaw_syntax cover
  rcases syntaxOk with ⟨markers,size,triples⟩
  simp only [MatchingInputValidation.validRaw,Bool.and_eq_true,List.all_eq_true,
    beq_iff_eq,decide_eq_true_eq]
  refine ⟨markers,?_⟩
  intro row member
  have valid:=triples row member
  refine ⟨valid.1,?_⟩
  intro value inside
  have bounded:=valid.2.2.2 value inside
  omega

def inputRaw (cover : X3CEncoding.Input) : MatchingVerification.Raw :=
  MatchingInputValidation.inputRaw (ThreeDMEncoding.fromRaw (X3CEncoding.toRaw cover))

theorem toRaw_inputRaw (cover : X3CEncoding.Input) :
    MatchingVerification.toRaw (inputRaw cover)=X3CEncoding.toRaw cover := by
  rw [inputRaw,MatchingInputValidation.toRaw_inputRaw]
  exact MatchingInputValidation.validRaw_reencode _ (matching_validRaw cover)

theorem inputRaw_encode (cover : X3CEncoding.Input) :
    MatchingVerification.rawCodec.encode (inputRaw cover)=X3CEncoding.codec.encode cover := by
  rw [MatchingVerification.rawCodec_encode,toRaw_inputRaw]
  rfl

theorem validInput_iff (input : List Bool) : validInput input=true ↔
    ∃ cover : X3CEncoding.Input,X3CEncoding.codec.encode cover=input := by
  refine ⟨validInput_sound input,?_⟩
  rintro ⟨cover,encoded⟩
  have decoded : MatchingVerification.rawCodec.decodeExact input=some (inputRaw cover) :=
    (MatchingVerification.rawCodec.decodeExact_iff _ _).mpr ((inputRaw_encode cover).trans encoded)
  simp only [validInput,decoded]
  apply (rawStatus_iff _).mpr
  rw [toRaw_inputRaw]
  exact X3CEncoding.toRaw_syntax cover

end Counting.External.CoverInputValidation
