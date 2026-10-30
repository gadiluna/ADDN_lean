import Counting.HardnessNetworkMachineContinuation
import Counting.ExternalCoverNormalizeComplete

namespace Counting.HardnessNetworkMachine

/-- The concrete reduction first removes duplicate triples and pads the
explicit universe, then constructs all serialized network matrices. -/
def normalizedNetwork (word : List Bool) : List Bool :=
  networkTransform (External.CoverNormalization.normalizeWord word)

theorem networkValue_correct (input : X3CEncoding.Input)
    (large : 2 ≤ input.1) (distinct : Function.Injective input.2.2.triples) :
    Encoding.BinarySomeAgentKnows (networkValue input) ↔
      ¬X3CEncoding.BinaryX3C (X3CEncoding.codec.encode input) := by
  let data : X3C.Instance input.1 input.2.1 :=
    ⟨input.2.2.triples,input.2.2.triple_card,distinct⟩
  have same : networkValue input=HardnessEncoded.networkBits data :=
    networkWord_coefficients data
  rw [same,HardnessEncoded.networkBits_correct data large,X3CEncoding.encoded_yes_iff]
  rfl

theorem normalizedNetwork_correct (word : List Bool) :
    Encoding.BinarySomeAgentKnows (normalizedNetwork word) ↔ ¬X3CEncoding.BinaryX3C word := by
  obtain ⟨input,encoded,large,distinct⟩:=External.CoverNormalization.normalizeWord_parameters word
  unfold normalizedNetwork
  rw [←encoded,networkTransform_encoded,networkValue_correct input large distinct]
  rw [encoded,External.CoverNormalization.normalizeWord_yes_iff]

/-- Every emitted instance is valid, has one leader, and uses loopless
round graphs. This also covers malformed source bitwords. -/
theorem normalizedNetwork_restricted (word : List Bool) :
    ∃ target,Encoding.decodeNetwork? (normalizedNetwork word)=some target ∧
      Encoding.inputLeaderCount target=1 ∧
      ∀ r, 0 < r → r ≤ target.rounds.size → ∀ agent : Encoding.InputAgent target,
        Encoding.inputGraph target r agent agent=0 := by
  obtain ⟨input,encoded,large,distinct⟩:=External.CoverNormalization.normalizeWord_parameters word
  let data : X3C.Instance input.1 input.2.1 :=
    ⟨input.2.2.triples,input.2.2.triple_card,distinct⟩
  have same : normalizedNetwork word=HardnessEncoded.networkBits data := by
    unfold normalizedNetwork
    rw [←encoded,networkTransform_encoded]
    exact networkWord_coefficients data
  refine ⟨HardnessEncoded.input data,?_,HardnessEncoded.input_leaderCount data,?_⟩
  · rw [same]
    exact (Encoding.decodeNetwork_iff _ _).mpr ⟨rfl,HardnessEncoded.input_valid data large⟩
  · intro r positive within agent
    rw [HardnessEncoded.input_rounds] at within
    exact HardnessEncoded.input_loopless data r positive within agent

end Counting.HardnessNetworkMachine
