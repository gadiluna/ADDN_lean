import Counting.HardnessVistaRawReduction

namespace Counting.HardnessVistaRaw

/-- Normalization supplies an actual admissible, nonempty typed network
on every source bitword, including words outside the X3C grammar. -/
theorem normalizedNetwork_target (word : List Bool) :
    ∃ input : Simulation.Input,
      Encoding.networkInput.encode input=HardnessNetworkMachine.normalizedNetwork word ∧
      Encoding.networkValid input=true ∧ 0 < input.leaders.size ∧
      Encoding.inputLeaderCount input=1 ∧
      normalizedVista word=firstWord input := by
  obtain ⟨input,decoded,leaders,_⟩ := HardnessNetworkMachine.normalizedNetwork_restricted word
  obtain ⟨encoded,valid⟩ := (Encoding.decodeNetwork_iff _ _).mp decoded
  refine ⟨input,encoded,valid,((Encoding.networkValid_iff input).mp valid).1,leaders,?_⟩
  rw [normalizedVista,←encoded,extractFirst_encoded]

end Counting.HardnessVistaRaw
