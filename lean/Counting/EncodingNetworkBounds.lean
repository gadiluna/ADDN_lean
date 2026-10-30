import Counting.EncodingNetworkSemantics
import Counting.CountingSizeEncoding

namespace Counting.Encoding
open Executable

private theorem array_get_mem {A : Type} (values : Array A) (i : Nat) (inside : i < values.size) :
    values[i] ∈ values.toList := by
  exact List.mem_iff_getElem.mpr ⟨i, by simpa only [Array.length_toList] using inside,
    Array.getElem_toList inside⟩

/-- Every matrix entry, including the zero returned for malformed indexes,
has binary length bounded by the length of the explicit network input. -/
theorem matrixEdge_bits_le_input (input : Simulation.Input) (graph : Simulation.RoundGraph)
    (present : graph ∈ input.rounds.toList) (a b : InputAgent input) :
    (matrixEdge graph input.leaders.size a b).size ≤ (networkInput.encode input).length := by
  by_cases row : a.val < graph.size
  · rw [matrixEdge, Array.getElem?_eq_getElem row, Option.getD_some]
    by_cases column : b.val < graph[a.val].size
    · rw [Array.getElem?_eq_getElem column, Option.getD_some]
      exact network_arc_bits_le_length input graph present graph[a.val] (array_get_mem graph a.val row)
        graph[a.val][b.val] (array_get_mem graph[a.val] b.val column)
    · rw [Array.getElem?_eq_none (by omega), Option.getD_none]
      simp
  · simp only [matrixEdge, Array.getElem?_eq_none (by omega : graph.size ≤ a.val), Option.getD_none]
    simp

theorem inputGraph_bits_le_input (input : Simulation.Input) (r : Nat)
    (positive : 0 < r) (within : r ≤ input.rounds.size) (a b : InputAgent input) :
    (inputGraph input r a b).size ≤ (networkInput.encode input).length := by
  let index : Fin input.rounds.size := ⟨r-1, by omega⟩
  have equal : index.val+1 = r := by dsimp [index]; omega
  rw [← equal, inputGraph_listed input index]
  exact matrixEdge_bits_le_input input input.rounds[index.val]
    (array_get_mem input.rounds index.val index.isLt) a b

theorem inputGraph_bundle_bound (input : Simulation.Input) (r : Nat)
    (positive : 0 < r) (within : r ≤ input.rounds.size) (a b : InputAgent input) :
    inputGraph input r a b ≤ 2^(networkInput.encode input).length :=
  (Nat.size_le.mp (inputGraph_bits_le_input input r positive within a b)).le

/-- A uniform arc-mass envelope is exponential in input length, but its
binary length is linear in that length. -/
theorem inputGraph_mass_bound (input : Simulation.Input) (r : Nat)
    (positive : 0 < r) (within : r ≤ input.rounds.size) :
    arcMass (inputGraph input) r ≤ input.leaders.size^2 * 2^(networkInput.encode input).length := by
  simpa only [InputAgent, Fintype.card_fin] using arcMass_le_of_bundle_bound (inputGraph input) r
    (2^(networkInput.encode input).length) (inputGraph_bundle_bound input r positive within)

theorem input_mass_bits_le (input : Simulation.Input) :
    Nat.size (input.leaders.size^2 * 2^(networkInput.encode input).length) ≤
      3*(networkInput.encode input).length+1 := by
  have bits := square_times_power_size_polynomial input.leaders.size (networkInput.encode input).length
  have agents := network_agents_le_length input
  omega

/-- An explicit monotone polynomial dominates the physical DAG codec bound
when population, rounds and label lengths are controlled by input length. -/
theorem network_vista_polynomial_arithmetic (n t B L : Nat)
    (agents : n ≤ L) (rounds : t ≤ L) (labels : B ≤ 3*L+1) :
    (t+1)*n * (8*(t+(t+1)*n+B+n+1)+9+n*(4*(t+(t+1)*n+B+n+1)+2))+2 ≤
      200*(L+1)^5 := by
  calc
    _ ≤ (L+1)*L * (8*(L+(L+1)*L+(3*L+1)+L+1)+9+L*(4*(L+(L+1)*L+(3*L+1)+L+1)+2))+2 := by
      gcongr
    _ ≤ _ := by ring_nf; omega

/-- Every actual shared vista computed from the explicit input has a
polynomial-size invertible binary encoding, uniformly over its observers.
No connectivity premise is needed for this representation bound. -/
theorem input_vista_encoding_length (input : Simulation.Input) (observer : InputAgent input) :
    let v := physicalVistaRun (inputGraph input) (inputLeader input) input.rounds.size observer
    (vista.encode v).length ≤ 200*((networkInput.encode input).length+1)^5 := by
  let v := physicalVistaRun (inputGraph input) (inputLeader input) input.rounds.size observer
  obtain ⟨valid, depth, physical⟩ := input_vista_correct input observer
  have bound := physical_vista_encoding_length (inputGraph input) (inputLeader input)
    input.rounds.size observer v valid depth physical
    (input.leaders.size^2 * 2^(networkInput.encode input).length) (inputGraph_mass_bound input)
  dsimp only at bound ⊢
  have polynomial := network_vista_polynomial_arithmetic input.leaders.size input.rounds.size
    (Nat.size (input.leaders.size^2 * 2^(networkInput.encode input).length))
    (networkInput.encode input).length (network_agents_le_length input) (network_rounds_le_length input)
    (input_mass_bits_le input)
  exact bound.trans (by simpa only [InputAgent, Fintype.card_fin] using polynomial)

end Counting.Encoding
