import Counting.NetworkCertificateRaw
import Counting.EncodingNetworkRecognition

namespace Counting.NetworkCertificate
open Encoding

/-- Invalid network input is accepted by the complementary verifier
without inspecting its witness. Valid input requires the compact list of
two-order certificates, checked against the computed DAG for every agent. -/
def binaryRawNetworkComplementVerifier (bits witness : List Bool) : Bool :=
  match decodeNetwork? bits with
  | none => true
  | some input => match networkWitness.decodeExact witness with
      | none => false
      | some certificates => verifyRawNetworkWitness input certificates

theorem binaryRawNetworkComplementVerifier_sound (bits witness : List Bool)
    (accepted : binaryRawNetworkComplementVerifier bits witness = true) :
    ¬ BinarySomeAgentKnows bits := by
  unfold binaryRawNetworkComplementVerifier at accepted
  unfold BinarySomeAgentKnows
  cases decoded : decodeNetwork? bits with
  | none => simp only [not_false_eq_true]
  | some input =>
      rw [decoded] at accepted
      cases parsed : networkWitness.decodeExact witness with
      | none => simp only [parsed, Bool.false_eq_true] at accepted
      | some certificates =>
          rw [parsed] at accepted
          exact verifyRawNetworkWitness_sound input certificates accepted

theorem binaryRawNetwork_complement_iff (bits : List Bool) :
    ¬ BinarySomeAgentKnows bits ↔ ∃ witness : List Bool,
      witness.length ≤ (20 * 204 ^ 3 + 3) * (bits.length + 1) ^ 16 ∧
      binaryRawNetworkComplementVerifier bits witness = true := by
  constructor
  · intro negative
    cases decoded : decodeNetwork? bits with
    | none =>
        exact ⟨[], Nat.zero_le _, by simp only [binaryRawNetworkComplementVerifier, decoded]⟩
    | some input =>
        obtain ⟨same, valid⟩ := (decodeNetwork_iff bits input).mp decoded
        have no : ¬ InputSomeAgentKnows input := by
          simpa only [BinarySomeAgentKnows, decoded] using negative
        obtain ⟨certificates, checked, bounded⟩ := verifyRawNetworkWitness_complete input valid no
        refine ⟨networkWitness.encode certificates, ?_, ?_⟩
        · simpa only [same] using bounded
        · rw [binaryRawNetworkComplementVerifier, decoded,
            (networkWitness.decodeExact_iff _ _).mpr rfl]
          exact checked
  · rintro ⟨witness, _, accepted⟩
    exact binaryRawNetworkComplementVerifier_sound bits witness accepted


end Counting.NetworkCertificate
