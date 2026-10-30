import Counting.EncodingNetworkRecognition

/-! A single alternate order per listed agent, as in the paper's network
certificate. The selection below discards one of the two bounded orders
without increasing the complete serialized witness length. -/
namespace Counting.Encoding

def alternateOrder (population : Nat) (pair : TwoOrderData) : Nat × List Nat :=
  if pair.1.1 = population then pair.2 else pair.1

theorem alternateOrder_correct (v : Executable.Vista) (ell population : Nat) (pair : TwoOrderData)
    (accepted : verifyTwoOrders v ell pair = true) :
    (alternateOrder population pair).1 ≠ population ∧
      RealizabilityVerifier.verify v (alternateOrder population pair).2.toArray ell
        (alternateOrder population pair).1 = true := by
  obtain ⟨different, first, second⟩ := (verifyTwoOrders_iff v ell pair).mp accepted
  unfold alternateOrder
  split
  · rename_i same
    exact ⟨by omega, second⟩
  · rename_i other
    exact ⟨other, first⟩

theorem alternateOrder_length_le (population : Nat) (pair : TwoOrderData) :
    (orderWitness.encode (alternateOrder population pair)).length ≤
      (twoOrderWitness.encode pair).length := by
  rw [twoOrderWitness_length]
  unfold alternateOrder
  split <;> omega

def alternateNetworkWitness : Codec (List (Nat × List Nat)) := list orderWitness

theorem alternateNetworkWitness_length_le (population : Nat) (pairs : List TwoOrderData) :
    (alternateNetworkWitness.encode (pairs.map (alternateOrder population))).length ≤
      (networkWitness.encode pairs).length := by
  have payload : ∀ pairs : List TwoOrderData,
      (pairs.map (fun pair => (orderWitness.encode (alternateOrder population pair)).length)).sum ≤
      (pairs.map (fun pair => (twoOrderWitness.encode pair).length)).sum := by
    intro pairs
    induction pairs with
    | nil => simp
    | cons pair pairs ih =>
        simp only [List.map_cons, List.sum_cons]
        exact Nat.add_le_add (alternateOrder_length_le population pair) ih
  rw [alternateNetworkWitness, networkWitness, list_length, list_length]
  simp only [List.length_map, List.map_map]
  exact Nat.add_le_add_left (payload pairs) _

/-- Complete encoded alternate-order certificates, one per physical agent.
Every selected order differs from the input population, and the bound
includes all list framing, order fields and anonymity counts. -/
theorem network_alternate_encoded_witnesses (input : Simulation.Input)
    (valid : networkValid input = true) (negative : ¬ InputSomeAgentKnows input) :
    ∃ witness : List (Nat × List Nat), witness.length = input.leaders.size ∧
      (∀ agent : InputAgent input, ∃ certificate, witness[agent.val]? = some certificate ∧
        certificate.1 ≠ input.leaders.size ∧
        RealizabilityVerifier.verify (agentVista input agent) certificate.2.toArray
          (inputLeaderCount input) certificate.1 = true) ∧
      (alternateNetworkWitness.encode witness).length ≤
        (20*204^3+3) * ((networkInput.encode input).length+1)^16 := by
  obtain ⟨pairs, checked, bounded⟩ := verifyNetworkWitness_complete input valid negative
  obtain ⟨length, each⟩ := (verifyNetworkWitness_iff input pairs).mp checked
  refine ⟨pairs.map (alternateOrder input.leaders.size), by simpa only [List.length_map] using length,
    ?_, (alternateNetworkWitness_length_le input.leaders.size pairs).trans bounded⟩
  intro agent
  obtain ⟨pair, lookup, accepted⟩ := each agent
  refine ⟨alternateOrder input.leaders.size pair, ?_,
    alternateOrder_correct _ _ _ _ accepted⟩
  simp only [List.getElem?_map, lookup, Option.map_some]

end Counting.Encoding
