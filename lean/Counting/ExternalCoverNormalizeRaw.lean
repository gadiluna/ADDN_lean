import Counting.ExternalCoverNormalizeSpec
import Counting.ExternalCoverNormalizePadding
import Counting.ExternalCoverInputValidity
import Counting.X3CEncodingNormalize

namespace Counting.External.CoverNormalization
set_option backward.isDefEq.respectTransparency false

def normalizedRaw (raw : MatchingVerification.Raw) : MatchingVerification.Raw :=
  (List.replicate (raw.1.length+6) true,paddingRows raw.1.length++freshRows [] raw.2)

theorem clauseToRaw_injective : Function.Injective MatchingVerification.clauseToRaw := by
  rintro ⟨⟨⟩,a,b,c⟩ ⟨⟨⟩,d,e,f⟩ equal
  simp only [MatchingVerification.clauseToRaw,List.cons.injEq,and_true] at equal
  rcases equal with ⟨rfl,rfl,rfl⟩
  rfl

/-- The actual fixed-width parser representation, first-occurrence loop and
forced padding agree exactly with the original typed normalization. -/
theorem normalizedRaw_toRaw (input : X3CEncoding.Input) :
    MatchingVerification.toRaw (normalizedRaw (CoverInputValidation.inputRaw input))=
      X3CEncoding.toRaw (X3CEncoding.normalizedInput input) := by
  have original := CoverInputValidation.toRaw_inputRaw input
  have universeEq : (CoverInputValidation.inputRaw input).1=List.replicate (3*input.1) true :=
    congrArg Prod.fst original
  have rows : (CoverInputValidation.inputRaw input).2.map MatchingVerification.clauseToRaw=
      List.ofFn (X3CEncoding.rawRows input.2.2) := by
    calc
      _=(X3CEncoding.inputTriples input).map X3CEncoding.tripleRaw := congrArg Prod.snd original
      _=_ := by rw [X3CEncoding.inputTriples,List.map_ofFn];rfl
  rw [X3CEncoding.normalizedInput_toRaw]
  apply Prod.ext
  · simp only [MatchingVerification.toRaw,normalizedRaw,universeEq,List.length_replicate]
    congr 1
  · simp only [MatchingVerification.toRaw,normalizedRaw,List.map_append,
      freshRows_map MatchingVerification.clauseToRaw clauseToRaw_injective,List.map_nil,rows,
      freshRows_firstIndices,universeEq,List.length_replicate,paddingRows,List.map_cons,List.map_nil]
    simp [consecutiveRow,MatchingVerification.clauseToRaw,X3CEncoding.freshRow,Nat.mul_add]

theorem normalizedRaw_encoded (input : X3CEncoding.Input) :
    MatchingVerification.rawCodec.encode (normalizedRaw (CoverInputValidation.inputRaw input))=
      X3CEncoding.codec.encode (X3CEncoding.normalizedInput input) := by
  rw [MatchingVerification.rawCodec_encode,normalizedRaw_toRaw]
  rfl

end Counting.External.CoverNormalization
