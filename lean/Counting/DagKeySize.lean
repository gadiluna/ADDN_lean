import Counting.DagKeyEncoding

namespace Counting.Executable

theorem sequence_key_length (node : Node) :
    (Encoding.sequence Encoding.natural node.key).length≤(Encoding.node.encode node).length+2 := by
  have leaderBound : (Encoding.natural.encode (if node.leader then 1 else 0)).length≤3 := by
    cases node.leader <;> decide
  rw [sequence_key]
  simp only [List.length_append,Encoding.node_length,Encoding.nodeBits,
    Encoding.natural_length,Encoding.sequence_length,Encoding.product] at leaderBound ⊢
  omega

end Counting.Executable
