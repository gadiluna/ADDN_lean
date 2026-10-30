import Counting.StackEncodingParserFixedBit
import Counting.StackEncodingParserTransport
import Counting.ExternalSATParser
import Counting.ExternalThreeSATEncoding

namespace Counting.External.ThreeSATVerification
open StackMachine.EncodingPrograms

abbrev HeaderFields := Unit×Unit×Unit×Unit×Unit
abbrev RawLiteral := Nat×Bool
abbrev RawClause := Unit×RawLiteral×RawLiteral×RawLiteral
abbrev Raw := List Bool×List RawClause

def headerFieldsCodec : Encoding.Codec HeaderFields :=
  Encoding.product (Encoding.fixedBit true) (Encoding.product (Encoding.fixedBit true)
    (Encoding.product (Encoding.fixedBit true) (Encoding.product (Encoding.fixedBit true) (Encoding.fixedBit false))))

def headerFieldsParser : VerifiedParser 15 0 1 2 HeaderFields headerFieldsCodec :=
  (fixedBitParser true 15 0 1 2 (by decide) (by decide) (by decide)).product (by decide) (by decide) (by decide)
    ((fixedBitParser true 15 0 1 2 (by decide) (by decide) (by decide)).product (by decide) (by decide) (by decide)
      ((fixedBitParser true 15 0 1 2 (by decide) (by decide) (by decide)).product (by decide) (by decide) (by decide)
        ((fixedBitParser true 15 0 1 2 (by decide) (by decide) (by decide)).product (by decide) (by decide) (by decide)
          (fixedBitParser false 15 0 1 2 (by decide) (by decide) (by decide)))))

def headerCodec : Encoding.Codec Unit :=
  Encoding.transport headerFieldsCodec (fun _ => ((),(),(),(),())) (fun _ => ()) (fun _ => Subsingleton.elim _ _)

def headerParser : VerifiedParser 15 0 1 2 Unit headerCodec :=
  headerFieldsParser.transport (fun _ => ((),(),(),(),())) (fun _ => ())
    (fun _ => Subsingleton.elim _ _) (fun _ => Subsingleton.elim _ _)

def literalCodec : Encoding.Codec RawLiteral := Encoding.product Encoding.natural Encoding.boolean
def clauseCodec : Encoding.Codec RawClause :=
  Encoding.product headerCodec (Encoding.product literalCodec (Encoding.product literalCodec literalCodec))
def rawCodec : Encoding.Codec Raw :=
  Encoding.product (Encoding.list Encoding.boolean) (Encoding.list clauseCodec)

def clauseParser : VerifiedParser 15 0 1 2 RawClause clauseCodec :=
  headerParser.product (by decide) (by decide) (by decide)
    (SATVerification.literalParser.product (by decide) (by decide) (by decide)
      (SATVerification.literalParser.product (by decide) (by decide) (by decide) SATVerification.literalParser))

def clauseToRaw (clause : RawClause) : List RawLiteral := [clause.2.1,clause.2.2.1,clause.2.2.2]
def toRaw (raw : Raw) : CNFEncoding.Raw := (raw.1,raw.2.map clauseToRaw)

@[simp] theorem clause_encode (clause : RawClause) :
    clauseCodec.encode clause=(Encoding.list literalCodec).encode (clauseToRaw clause) := by
  rcases clause with ⟨⟨⟩,a,b,c⟩
  change Encoding.natural.encode 3 ++ (literalCodec.encode a ++ (literalCodec.encode b ++ literalCodec.encode c))=
    Encoding.natural.encode 3 ++ (literalCodec.encode a ++ (literalCodec.encode b ++ (literalCodec.encode c ++ [])))
  simp only [List.append_nil]

def formulaParser : VerifiedParser 15 0 1 2 (List RawClause) (Encoding.list clauseCodec) :=
  listParser 0 DagParser.outerRoles clauseParser (by decide) (by
    intro clause
    rw [clause_encode,Encoding.list_length]
    omega)

def rawParser : VerifiedParser 15 0 1 2 Raw rawCodec :=
  SATVerification.tableParser.product (by decide) (by decide) (by decide) formulaParser

theorem rawParser_exponent_le_four : rawParser.exponent ≤ 4 := by decide

theorem sequence_encode (clauses : List RawClause) :
    Encoding.sequence clauseCodec clauses=
      Encoding.sequence (Encoding.list literalCodec) (clauses.map clauseToRaw) := by
  induction clauses with
  | nil => rfl
  | cons clause rest ih => simp only [List.map_cons,Encoding.sequence,clause_encode,ih]

theorem rawCodec_encode (raw : Raw) : rawCodec.encode raw=CNFEncoding.rawCodec.encode (toRaw raw) := by
  simp only [rawCodec,CNFEncoding.rawCodec,Encoding.product,Encoding.list,toRaw,List.length_map,sequence_encode]
  rfl

def clauseFromRaw : List RawLiteral → RawClause
  | a::b::c::_ => ((),a,b,c)
  | _ => ((),(0,false),(0,false),(0,false))

theorem clauseToRaw_fromRaw (clause : List RawLiteral) (three : clause.length=3) :
    clauseToRaw (clauseFromRaw clause)=clause := by
  cases clause with
  | nil => simp at three
  | cons a rest =>
    cases rest with
    | nil => simp at three
    | cons b rest =>
      cases rest with
      | nil => simp at three
      | cons c rest =>
        have empty : rest=[] := List.length_eq_zero_iff.mp (by simpa using three)
        subst rest
        rfl

theorem exactEffect_iff (input : List Bool) :
    rawParser.exactEffect input=true ↔ ∃ raw : CNFEncoding.Raw,
      CNFEncoding.rawCodec.encode raw=input ∧ ∀ clause∈raw.2,clause.length=3 := by
  rw [rawParser.exactEffect_decodeExact,Option.isSome_iff_exists]
  constructor
  · rintro ⟨raw,decoded⟩
    have encoded := (rawCodec.decodeExact_iff input raw).mp decoded
    refine ⟨toRaw raw,(rawCodec_encode raw).symm.trans encoded,?_⟩
    intro clause member
    obtain ⟨original,_member,rfl⟩ := List.mem_map.mp member
    rfl
  · rintro ⟨raw,encoded,three⟩
    let value : Raw := (raw.1,raw.2.map clauseFromRaw)
    have same : toRaw value=raw := by
      apply Prod.ext
      · rfl
      · change (raw.2.map clauseFromRaw).map clauseToRaw=raw.2
        rw [List.map_map]
        conv_rhs => rw [←List.map_id raw.2]
        apply List.map_congr_left
        intro clause member
        exact clauseToRaw_fromRaw clause (three clause member)
    refine ⟨value,(rawCodec.decodeExact_iff input value).mpr ?_⟩
    rw [rawCodec_encode,same,encoded]

theorem exactEffect_encoded (input : CNFInput) :
    rawParser.exactEffect (CNFEncoding.codec.encode input)=true ↔
      ∀ clause∈input.2,clause.length=3 := by
  rw [exactEffect_iff]
  constructor
  · rintro ⟨raw,encoded,three⟩
    have same : raw=CNFEncoding.toRaw input := CNFEncoding.rawCodec.injective encoded
    subst raw
    simpa [CNFEncoding.toRaw] using three
  · intro three
    exact ⟨CNFEncoding.toRaw input,rfl,by simpa [CNFEncoding.toRaw] using three⟩

end Counting.External.ThreeSATVerification
