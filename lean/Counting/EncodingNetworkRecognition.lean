import Counting.EncodingNetworkWitness

namespace Counting.Encoding

/-- Invalid encodings and inadmissible networks have a negative answer. -/
def BinarySomeAgentKnows (bits : List Bool) : Prop :=
  match decodeNetwork? bits with
  | none => False
  | some input => InputSomeAgentKnows input

/-- Invalid network input is accepted by the complementary verifier
without inspecting its witness. Valid input requires the compact list of
two-order certificates, checked against the computed DAG for every agent. -/
def binaryNetworkComplementVerifier (bits witness : List Bool) : Bool :=
  match decodeNetwork? bits with
  | none => true
  | some input => match networkWitness.decodeExact witness with
      | none => false
      | some certificates => verifyNetworkWitness input certificates

theorem binaryNetworkComplementVerifier_sound (bits witness : List Bool)
    (accepted : binaryNetworkComplementVerifier bits witness = true) :
    ¬ BinarySomeAgentKnows bits := by
  unfold binaryNetworkComplementVerifier at accepted
  unfold BinarySomeAgentKnows
  cases decoded : decodeNetwork? bits with
  | none => simp only [not_false_eq_true]
  | some input =>
      rw [decoded] at accepted
      cases parsed : networkWitness.decodeExact witness with
      | none => simp only [parsed, Bool.false_eq_true] at accepted
      | some certificates =>
          rw [parsed] at accepted
          exact verifyNetworkWitness_sound input certificates accepted

theorem binaryNetwork_complement_iff (bits : List Bool) :
    ¬ BinarySomeAgentKnows bits ↔ ∃ witness : List Bool,
      witness.length ≤ (20 * 204 ^ 3 + 3) * (bits.length + 1) ^ 16 ∧
      binaryNetworkComplementVerifier bits witness = true := by
  constructor
  · intro negative
    cases decoded : decodeNetwork? bits with
    | none =>
        exact ⟨[], Nat.zero_le _, by simp only [binaryNetworkComplementVerifier, decoded]⟩
    | some input =>
        obtain ⟨same, valid⟩ := (decodeNetwork_iff bits input).mp decoded
        have no : ¬ InputSomeAgentKnows input := by
          simpa only [BinarySomeAgentKnows, decoded] using negative
        obtain ⟨certificates, checked, bounded⟩ := verifyNetworkWitness_complete input valid no
        refine ⟨networkWitness.encode certificates, ?_, ?_⟩
        · simpa only [same] using bounded
        · rw [binaryNetworkComplementVerifier, decoded,
            (networkWitness.decodeExact_iff _ _).mpr rfl]
          exact checked
  · rintro ⟨witness, _, accepted⟩
    exact binaryNetworkComplementVerifier_sound bits witness accepted

end Counting.Encoding
