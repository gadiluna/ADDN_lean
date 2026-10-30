import Counting.EncodingNetworkViews

namespace Counting.Encoding

/-- The declared leader total counts an explicitly listed subset of agents. -/
theorem inputLeaderCount_le_agents (input : Simulation.Input) :
    inputLeaderCount input ≤ input.leaders.size := by
  simpa only [inputLeaderCount, Finset.card_univ, InputAgent, Fintype.card_fin] using
    Finset.card_filter_le (Finset.univ : Finset (InputAgent input))
      (fun agent => inputLeader input agent = true)

theorem inputLeaderCount_le_length (input : Simulation.Input) :
    inputLeaderCount input ≤ (networkInput.encode input).length :=
  (inputLeaderCount_le_agents input).trans (network_agents_le_length input)

theorem inputLeaderCount_bits_le_length (input : Simulation.Input) :
    (inputLeaderCount input).size ≤ (networkInput.encode input).length :=
  (Nat.size_le.mpr Nat.lt_two_pow_self).trans (inputLeaderCount_le_length input)

end Counting.Encoding
