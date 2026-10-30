import Counting.NetworkCertificateSpec
import Counting.DagRawPhysical

namespace Counting.NetworkCertificate
open Encoding

def verifyRawNetworkWitness (input : Simulation.Input) (certificates : List TwoOrderData) : Bool :=
  check (inputLeaderCount input) (rawInputVistas input).toList certificates

theorem verifyRawNetworkWitness_iff (input : Simulation.Input) (certificates : List TwoOrderData) :
    verifyRawNetworkWitness input certificates=true ↔
      certificates.length=input.leaders.size ∧ ∀ agent : InputAgent input,
        ∃ certificate, certificates[agent.val]?=some certificate ∧
          verifyTwoOrders (rawAgentVista input agent) (inputLeaderCount input) certificate=true := by
  rw [verifyRawNetworkWitness,check_iff]
  constructor
  · rintro ⟨length,checked⟩
    refine ⟨by simpa using length.symm,?_⟩
    intro agent
    obtain ⟨certificate,lookup,accepted⟩ := checked ⟨agent.val,by simp⟩
    exact ⟨certificate,lookup,by simpa only [rawAgentVista,Array.getElem_toList] using accepted⟩
  · rintro ⟨length,checked⟩
    refine ⟨by simpa using length.symm,?_⟩
    intro agent
    obtain ⟨certificate,lookup,accepted⟩ := checked ⟨agent.val,by simpa using agent.isLt⟩
    exact ⟨certificate,lookup,by simpa only [rawAgentVista,Array.getElem_toList] using accepted⟩

theorem verifyRawNetworkWitness_sound (input : Simulation.Input) (witness : List TwoOrderData)
    (accepted : verifyRawNetworkWitness input witness = true) : ¬ InputSomeAgentKnows input := by
  rintro ⟨_, _, agent, unique⟩
  obtain ⟨certificate, _, checked⟩ := ((verifyRawNetworkWitness_iff input witness).mp accepted).2 agent
  have negative := (verifyTwoOrders_sound _ _ _ checked).2
  exact negative ((rawAgentVista_atMostOne_iff input agent).mpr unique)

theorem verifyRawNetworkWitness_complete (input : Simulation.Input) (valid : networkValid input = true)
    (negative : ¬ InputSomeAgentKnows input) :
    ∃ witness : List TwoOrderData, verifyRawNetworkWitness input witness = true ∧
      (networkWitness.encode witness).length ≤
        (20 * 204 ^ 3 + 3) * ((networkInput.encode input).length + 1) ^ 16 := by
  classical
  let L := (networkInput.encode input).length
  have every : ∀ agent : InputAgent input,
      ¬ Realizability.AtMostOneVista (inputLeaderCount input) (rawAgentVista input agent).denotes := by
    intro agent unique
    exact negative ⟨valid, networkValid_admissible input valid, agent,
      (rawAgentVista_atMostOne_iff input agent).mp unique⟩
  have localWitness : ∀ agent : InputAgent input, ∃ witness : TwoOrderData,
      verifyTwoOrders (rawAgentVista input agent) (inputLeaderCount input) witness = true ∧
      (twoOrderWitness.encode witness).length ≤ 20 * 204 ^ 3 * (L + 1) ^ 15 := by
    intro agent
    obtain ⟨first, second, counts₁, counts₂, different, accepted₁, accepted₂, _, _, bound⟩ :=
      vista_complement_encoded_witnesses (rawAgentVista input agent)
        (rawInputVistas_correct input agent).1 (inputLeaderCount input) (every agent)
    refine ⟨((first, counts₁.toList), (second, counts₂.toList)), ?_, ?_⟩
    · apply (verifyTwoOrders_iff _ _ _).mpr
      exact ⟨different, by simpa only [Array.toArray_toList] using accepted₁,
        by simpa only [Array.toArray_toList] using accepted₂⟩
    · have inputBound := rawAgentVista_input_length input agent
      have positive : 1 ≤ (L + 1) ^ 5 := Nat.one_le_pow _ _ (by omega)
      have lifted : (vistaInput.encode (rawAgentVista input agent, inputLeaderCount input)).length + 1 ≤
          204 * (L + 1) ^ 5 := by dsimp only [L] at *; omega
      have cubed := Nat.pow_le_pow_left lifted 3
      rw [mul_pow, ← pow_mul] at cubed
      exact bound.trans (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left 20 cubed)
  choose certificates checked bounds using localWitness
  let witness := List.ofFn certificates
  have length : witness.length = input.leaders.size := List.length_ofFn
  refine ⟨witness, (verifyRawNetworkWitness_iff input witness).mpr ⟨length, ?_⟩, ?_⟩
  · intro agent
    refine ⟨certificates agent, ?_, checked agent⟩
    simp only [witness, List.getElem?_ofFn, Fin.isLt, dite_true, Fin.eta]
  · have sized := networkWitness_length_bound witness (20 * 204 ^ 3 * (L + 1) ^ 15) (by
      intro value present
      obtain ⟨agent, rfl⟩ := (List.mem_ofFn.mp present)
      exact bounds agent)
    rw [length] at sized
    have agents := network_agents_le_length input
    have header : input.leaders.size.size ≤ input.leaders.size := Nat.size_le.mpr Nat.lt_two_pow_self
    have product := Nat.mul_le_mul_right (20 * 204 ^ 3 * (L + 1) ^ 15) agents
    have power : L + 1 ≤ (L + 1) ^ 16 := Nat.le_pow (by norm_num)
    have larger : L * (20 * 204 ^ 3 * (L + 1) ^ 15) ≤
        20 * 204 ^ 3 * (L + 1) ^ 16 := by
      calc
        _ ≤ (L + 1) * (20 * 204 ^ 3 * (L + 1) ^ 15) := Nat.mul_le_mul_right _ (Nat.le_succ _)
        _ = _ := by ring
    dsimp only [L] at *
    omega


end Counting.NetworkCertificate
