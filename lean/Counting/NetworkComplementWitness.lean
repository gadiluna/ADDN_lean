import Counting.EncodingNetworkAlternate

/-! The paper's one-alternate-order certificate for an explicit network.
The binary boundary includes inadmissible networks and malformed words.
This file proves the exact verifier relation and witness size; it makes
no machine-time assertion for reconstructing the network's vistas. -/
namespace Counting.Encoding

theorem realizable_decode_iff (v : Executable.Vista) (ell order t : Nat)
    (H : FullHistory t) (depth : (v.node v.bottom).level=t)
    (history : Executable.decodeNode v t v.bottom=H) :
    Realizability.Realizable ell order v.denotes ↔ Realizability.Realizable ell order H := by
  subst t
  rw [←history]
  rfl

theorem agentVista_realizable (input : Simulation.Input) (valid : networkValid input=true)
    (agent : InputAgent input) :
    Realizability.Realizable (inputLeaderCount input) input.leaders.size
      (agentVista input agent).denotes := by
  obtain ⟨_,depth,history⟩ := inputVistas_correct input agent
  apply (realizable_decode_iff _ _ _ _ _ depth history).mpr
  simpa only [InputAgent,Fintype.card_fin,inputHistory] using
    Realizability.actual_history_realizable (inputLeaderCount input)
    (inputGraph input) (inputLeader input) input.rounds.size
    (networkValid_admissible input valid) agent

def verifyAlternateNetworkWitness (input : Simulation.Input)
    (witness : List (Nat × List Nat)) : Bool :=
  witness.length == input.leaders.size &&
    (List.finRange input.leaders.size).all (fun agent =>
      match witness[agent.val]? with
      | none => false
      | some certificate => !(certificate.1 == input.leaders.size) &&
          RealizabilityVerifier.verify (agentVista input agent) certificate.2.toArray
            (inputLeaderCount input) certificate.1)

theorem verifyAlternateNetworkWitness_iff (input : Simulation.Input)
    (witness : List (Nat × List Nat)) :
    verifyAlternateNetworkWitness input witness=true ↔
      witness.length=input.leaders.size ∧ ∀ agent : InputAgent input,
        ∃ certificate, witness[agent.val]?=some certificate ∧
          certificate.1 ≠ input.leaders.size ∧
          RealizabilityVerifier.verify (agentVista input agent) certificate.2.toArray
            (inputLeaderCount input) certificate.1=true := by
  simp only [verifyAlternateNetworkWitness,Bool.and_eq_true,beq_iff_eq,List.all_eq_true,
    List.mem_finRange,forall_true_left]
  apply and_congr_right'
  apply forall_congr'
  intro agent
  cases lookup : witness[agent.val]? with
  | none => simp
  | some certificate => simp

theorem verifyAlternateNetworkWitness_sound (input : Simulation.Input)
    (witness : List (Nat × List Nat))
    (accepted : verifyAlternateNetworkWitness input witness=true) :
    ¬ InputSomeAgentKnows input := by
  rintro ⟨valid,_,agent,unique⟩
  obtain ⟨certificate,_,different,verified⟩ :=
    ((verifyAlternateNetworkWitness_iff input witness).mp accepted).2 agent
  have uniqueVista := (agentVista_atMostOne_iff input agent).mpr unique
  exact different (uniqueVista (RealizabilityVerifier.verify_sound _ _ _ _ verified)
    (agentVista_realizable input valid agent))

theorem verifyAlternateNetworkWitness_complete (input : Simulation.Input)
    (valid : networkValid input=true) (negative : ¬ InputSomeAgentKnows input) :
    ∃ witness : List (Nat × List Nat), verifyAlternateNetworkWitness input witness=true ∧
      (alternateNetworkWitness.encode witness).length ≤
        (20*204^3+3)*((networkInput.encode input).length+1)^16 := by
  obtain ⟨witness,length,each,bound⟩ := network_alternate_encoded_witnesses input valid negative
  exact ⟨witness,(verifyAlternateNetworkWitness_iff input witness).mpr ⟨length,each⟩,bound⟩

/-- Invalid network inputs are negative instances of the original language,
so their complement accepts without asking for any certificate. -/
def binaryAlternateNetworkVerifier (bits witness : List Bool) : Bool :=
  match decodeNetwork? bits with
  | none => true
  | some input => match alternateNetworkWitness.decodeExact witness with
      | none => false
      | some certificates => verifyAlternateNetworkWitness input certificates

theorem binaryAlternateNetworkVerifier_sound (bits witness : List Bool)
    (accepted : binaryAlternateNetworkVerifier bits witness=true) :
    ¬ BinarySomeAgentKnows bits := by
  unfold binaryAlternateNetworkVerifier at accepted
  unfold BinarySomeAgentKnows
  cases decoded : decodeNetwork? bits with
  | none => simp
  | some input =>
    rw [decoded] at accepted
    cases parsed : alternateNetworkWitness.decodeExact witness with
    | none => simp [parsed] at accepted
    | some certificates =>
      rw [parsed] at accepted
      exact verifyAlternateNetworkWitness_sound input certificates accepted

/-- This is the exact certificate relation for the paper's network problem,
with one alternate order per physical agent and a bound on the serialized
certificate rather than on the magnitude of its numerical fields. -/
theorem binaryNetwork_alternate_complement_iff (bits : List Bool) :
    ¬ BinarySomeAgentKnows bits ↔ ∃ witness : List Bool,
      witness.length ≤ (20*204^3+3)*(bits.length+1)^16 ∧
      binaryAlternateNetworkVerifier bits witness=true := by
  constructor
  · intro negative
    cases decoded : decodeNetwork? bits with
    | none => exact ⟨[],Nat.zero_le _,by simp [binaryAlternateNetworkVerifier,decoded]⟩
    | some input =>
      obtain ⟨same,valid⟩ := (decodeNetwork_iff bits input).mp decoded
      have no : ¬ InputSomeAgentKnows input := by
        simpa only [BinarySomeAgentKnows,decoded] using negative
      obtain ⟨certificates,accepted,bound⟩ := verifyAlternateNetworkWitness_complete input valid no
      refine ⟨alternateNetworkWitness.encode certificates,by simpa only [same] using bound,?_⟩
      rw [binaryAlternateNetworkVerifier,decoded,
        (alternateNetworkWitness.decodeExact_iff _ _).mpr rfl]
      exact accepted
  · rintro ⟨witness,_,accepted⟩
    exact binaryAlternateNetworkVerifier_sound bits witness accepted

end Counting.Encoding
