import Counting.EncodingDag
import Counting.Simulation

/-! Binary network inputs list every agent's initial bit and every finite
round matrix explicitly. Multiplicities are encoded as binary naturals.
Malformed shapes are retained by the codec and rejected by validation. -/
namespace Counting.Encoding

/-- An invertible array codec, using the explicit list length prefix. -/
def array {A : Type} (codec : Codec A) : Codec (Array A) :=
  transport (list codec) Array.toList List.toArray (by intro values; simp)

theorem array_length {A : Type} (codec : Codec A) (values : Array A) :
    ((array codec).encode values).length = 2*values.size.size+1+
      (values.toList.map (fun value => (codec.encode value).length)).sum := by
  simp only [array, transport, list_length, Array.length_toList]

theorem array_length_positive {A : Type} (codec : Codec A) (values : Array A) :
    0 < ((array codec).encode values).length := by rw [array_length]; omega

theorem array_member_length_le {A : Type} (codec : Codec A) (values : Array A) (value : A)
    (present : value ∈ values.toList) :
    (codec.encode value).length ≤ ((array codec).encode values).length := by
  have bound : (codec.encode value).length ≤
      (values.toList.map (fun a => (codec.encode a).length)).sum :=
    List.single_le_sum (fun _ _ => Nat.zero_le _)
      (codec.encode value).length (List.mem_map.mpr ⟨value, present, rfl⟩)
  rw [array_length]
  omega

theorem array_size_le_length {A : Type} (codec : Codec A) (values : Array A)
    (positive : ∀ value ∈ values.toList, 0 < (codec.encode value).length) :
    values.size ≤ ((array codec).encode values).length := by
  have count := List.sum_le_sum (l := values.toList) (f := fun _ => 1)
    (g := fun value => (codec.encode value).length) (fun value member => positive value member)
  simp only [List.map_const', List.sum_replicate, Array.length_toList, smul_eq_mul, Nat.mul_one] at count
  rw [array_length]
  omega

def networkInput : Codec Simulation.Input :=
  transport (product (array boolean) (array (array (array natural))))
    (fun input => (input.leaders, input.rounds))
    (fun fields => ⟨fields.1, fields.2⟩)
    (by intro input; rfl)

theorem networkInput_roundtrip (input : Simulation.Input) (suffix : List Bool) :
    networkInput.decode (networkInput.encode input ++ suffix) = some (input, suffix) :=
  networkInput.roundtrip input suffix

theorem networkInput_injective : Function.Injective networkInput.encode := networkInput.injective

theorem networkInput_length (input : Simulation.Input) :
    (networkInput.encode input).length =
      ((array boolean).encode input.leaders).length +
      ((array (array (array natural))).encode input.rounds).length := by
  simp only [networkInput, transport, product, List.length_append]

/-- Explicitly listing the initial Boolean labels bounds the number of
agents by the binary input length, independently of matrix validity. -/
theorem network_agents_le_length (input : Simulation.Input) :
    input.leaders.size ≤ (networkInput.encode input).length := by
  have bound := array_size_le_length boolean input.leaders (by intro value _; simp [boolean])
  rw [networkInput_length]
  omega

/-- Every listed round has at least its matrix length prefix, even when
malformed, so the declared time horizon is also input-length bounded. -/
theorem network_rounds_le_length (input : Simulation.Input) :
    input.rounds.size ≤ (networkInput.encode input).length := by
  have bound := array_size_le_length (array (array natural)) input.rounds
    (fun value _ => array_length_positive _ value)
  rw [networkInput_length]
  omega

theorem network_arc_bits_le_length (input : Simulation.Input)
    (graph : Simulation.RoundGraph) (inGraphs : graph ∈ input.rounds.toList)
    (row : Array Nat) (inRows : row ∈ graph.toList)
    (count : Nat) (inRow : count ∈ row.toList) :
    count.size ≤ (networkInput.encode input).length := by
  have arc := array_member_length_le natural row count inRow
  have rows := array_member_length_le (array natural) graph row inRows
  have graphs := array_member_length_le (array (array natural)) input.rounds graph inGraphs
  rw [natural_length] at arc
  rw [networkInput_length]
  omega

end Counting.Encoding
