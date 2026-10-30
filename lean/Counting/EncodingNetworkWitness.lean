import Counting.EncodingRecognition
import Counting.EncodingNetworkProperties

/-! Actual compact complementary certificates for the explicit network
encoding. The checker computes the input's shared DAGs once, then verifies
two compatible orders for each listed agent. This file proves functional
correctness and serialized witness size, not a Turing-machine time bound. -/
namespace Counting.Encoding
open Executable

abbrev TwoOrderData := (Nat × List Nat) × (Nat × List Nat)

def networkWitness : Codec (List TwoOrderData) := list twoOrderWitness

def agentVista (input : Simulation.Input) (agent : InputAgent input) : Vista :=
  (inputVistas input)[agent.val]'(by rw [inputVistas_size]; exact agent.isLt)

theorem atMostOne_decode_iff (v : Vista) (ell t : Nat) (H : FullHistory t)
    (depth : (v.node v.bottom).level = t) (history : decodeNode v t v.bottom = H) :
    Realizability.AtMostOneVista ell v.denotes ↔ Realizability.AtMostOneVista ell H := by
  subst t
  rw [← history]
  rfl

theorem agentVista_atMostOne_iff (input : Simulation.Input) (agent : InputAgent input) :
    Realizability.AtMostOneVista (inputLeaderCount input) (agentVista input agent).denotes ↔
      Realizability.AtMostOneVista (inputLeaderCount input) (inputHistory input agent) := by
  obtain ⟨_, depth, history⟩ := inputVistas_correct input agent
  exact atMostOne_decode_iff _ _ _ _ depth history

theorem agentVista_input_length (input : Simulation.Input) (agent : InputAgent input) :
    (vistaInput.encode (agentVista input agent, inputLeaderCount input)).length ≤
      203 * ((networkInput.encode input).length + 1) ^ 5 := by
  have dag := inputVistas_encoding_length input agent
  have leaders := inputLeaderCount_bits_le_length input
  have power : (networkInput.encode input).length + 1 ≤
      ((networkInput.encode input).length + 1) ^ 5 := Nat.le_pow (by norm_num)
  rw [vistaInput_length]
  dsimp only [agentVista]
  nlinarith

def verifyNetworkWitness (input : Simulation.Input) (witness : List TwoOrderData) : Bool :=
  let vistas := inputVistas input
  witness.length == input.leaders.size &&
    (List.finRange input.leaders.size).all (fun agent =>
      match witness[agent.val]? with
      | none => false
      | some certificate => verifyTwoOrders
          (vistas[agent.val]'(by rw [inputVistas_size]; exact agent.isLt))
          (inputLeaderCount input) certificate)

theorem verifyNetworkWitness_iff (input : Simulation.Input) (witness : List TwoOrderData) :
    verifyNetworkWitness input witness = true ↔
      witness.length = input.leaders.size ∧ ∀ agent : InputAgent input,
        ∃ certificate, witness[agent.val]? = some certificate ∧
          verifyTwoOrders (agentVista input agent) (inputLeaderCount input) certificate = true := by
  simp only [verifyNetworkWitness, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    List.mem_finRange, forall_true_left]
  apply and_congr_right'
  apply forall_congr'
  intro agent
  cases lookup : witness[agent.val]? with
  | none => simp only [Bool.false_eq_true, reduceCtorEq, false_and, exists_false]
  | some certificate =>
      simp only [Option.some.injEq, agentVista]
      exact ⟨fun checked => ⟨certificate, rfl, checked⟩, fun ⟨_, same, checked⟩ => same ▸ checked⟩

def InputSomeAgentKnows (input : Simulation.Input) : Prop :=
  networkValid input = true ∧ Realizability.SomeAgentKnows (inputLeaderCount input)
    (inputGraph input) (inputLeader input) input.rounds.size

theorem verifyNetworkWitness_sound (input : Simulation.Input) (witness : List TwoOrderData)
    (accepted : verifyNetworkWitness input witness = true) : ¬ InputSomeAgentKnows input := by
  rintro ⟨_, _, agent, unique⟩
  obtain ⟨certificate, _, checked⟩ := ((verifyNetworkWitness_iff input witness).mp accepted).2 agent
  have negative := (verifyTwoOrders_sound _ _ _ checked).2
  exact negative ((agentVista_atMostOne_iff input agent).mpr unique)

theorem networkWitness_length_bound (witness : List TwoOrderData) (bound : Nat)
    (bounded : ∀ value ∈ witness, (twoOrderWitness.encode value).length ≤ bound) :
    (networkWitness.encode witness).length ≤
      2 * witness.length.size + 1 + witness.length * bound := by
  rw [networkWitness, list_length]
  apply Nat.add_le_add_left
  induction witness with
  | nil => simp only [List.map_nil, List.sum_nil, List.length_nil, Nat.zero_mul, le_refl]
  | cons head tail ih =>
      have first := bounded head List.mem_cons_self
      have rest := ih (fun value present => bounded value (List.mem_cons_of_mem head present))
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      nlinarith

theorem verifyNetworkWitness_complete (input : Simulation.Input) (valid : networkValid input = true)
    (negative : ¬ InputSomeAgentKnows input) :
    ∃ witness : List TwoOrderData, verifyNetworkWitness input witness = true ∧
      (networkWitness.encode witness).length ≤
        (20 * 204 ^ 3 + 3) * ((networkInput.encode input).length + 1) ^ 16 := by
  classical
  let L := (networkInput.encode input).length
  have every : ∀ agent : InputAgent input,
      ¬ Realizability.AtMostOneVista (inputLeaderCount input) (agentVista input agent).denotes := by
    intro agent unique
    exact negative ⟨valid, networkValid_admissible input valid, agent,
      (agentVista_atMostOne_iff input agent).mp unique⟩
  have localWitness : ∀ agent : InputAgent input, ∃ witness : TwoOrderData,
      verifyTwoOrders (agentVista input agent) (inputLeaderCount input) witness = true ∧
      (twoOrderWitness.encode witness).length ≤ 20 * 204 ^ 3 * (L + 1) ^ 15 := by
    intro agent
    obtain ⟨first, second, counts₁, counts₂, different, accepted₁, accepted₂, _, _, bound⟩ :=
      vista_complement_encoded_witnesses (agentVista input agent)
        (inputVistas_correct input agent).1 (inputLeaderCount input) (every agent)
    refine ⟨((first, counts₁.toList), (second, counts₂.toList)), ?_, ?_⟩
    · apply (verifyTwoOrders_iff _ _ _).mpr
      exact ⟨different, by simpa only [Array.toArray_toList] using accepted₁,
        by simpa only [Array.toArray_toList] using accepted₂⟩
    · have inputBound := agentVista_input_length input agent
      have positive : 1 ≤ (L + 1) ^ 5 := Nat.one_le_pow _ _ (by omega)
      have lifted : (vistaInput.encode (agentVista input agent, inputLeaderCount input)).length + 1 ≤
          204 * (L + 1) ^ 5 := by dsimp only [L] at *; omega
      have cubed := Nat.pow_le_pow_left lifted 3
      rw [mul_pow, ← pow_mul] at cubed
      exact bound.trans (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left 20 cubed)
  choose certificates checked bounds using localWitness
  let witness := List.ofFn certificates
  have length : witness.length = input.leaders.size := List.length_ofFn
  refine ⟨witness, (verifyNetworkWitness_iff input witness).mpr ⟨length, ?_⟩, ?_⟩
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

end Counting.Encoding
