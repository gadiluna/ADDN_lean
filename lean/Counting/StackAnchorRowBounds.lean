import Counting.StackAnchorRow

namespace Counting.StackMachine.AnchorRow

private theorem sequence_length_bound {α : Type} (codec : Encoding.Codec α) (values : List α) (bound : Nat)
    (bounded : ∀ value∈values,(codec.encode value).length ≤ bound) :
    (Encoding.sequence codec values).length ≤ values.length*bound := by
  induction values with
  | nil => simp [Encoding.sequence]
  | cons value values ih =>
    have head := bounded value (by simp)
    have rest := ih (by intro x member;exact bounded x (List.mem_cons_of_mem value member))
    simp only [Encoding.sequence,List.length_append,List.length_cons]
    nlinarith

private theorem node_length_mem (nodes : List Executable.Node) (node : Executable.Node) (member : node∈nodes) :
    (Encoding.node.encode node).length ≤ (Encoding.sequence Encoding.node nodes).length := by
  induction nodes with
  | nil => simp at member
  | cons first nodes ih =>
    simp only [Encoding.sequence,List.length_append]
    rcases List.mem_cons.mp member with rfl|inside
    · omega
    · have bound := ih inside;omega

theorem values_length (nodes : List Executable.Node) (query anchor : Nat) :
    (values nodes query anchor).length ≤ nodes.length := by
  simpa only [values,List.length_map,AnchorCoefficient.selectedNodes] using
    List.length_filter_le (fun node=>node.level==anchor) nodes

theorem nodes_length (nodes : List Executable.Node) :
    nodes.length ≤ (Encoding.sequence Encoding.node nodes).length := by
  induction nodes with
  | nil => rfl
  | cons node nodes ih =>
    have positive : 0<(Encoding.node.encode node).length := by
      rw [Encoding.node_length];unfold Encoding.nodeBits;omega
    simp only [Encoding.sequence,List.length_append,List.length_cons]
    omega

theorem stream_length (nodes : List Executable.Node) (query anchor limit : Nat)
    (inputBound : (Encoding.sequence Encoding.node nodes).length ≤ limit) :
    (Encoding.sequence (Encoding.framed Encoding.rational) (values nodes query anchor++[0])).length ≤
      ((values nodes query anchor).length+1)*(4000*(limit+1)+1) := by
  have bounded : ∀ value∈values nodes query anchor++[0],
      ((Encoding.framed Encoding.rational).encode value).length ≤ 4000*(limit+1)+1 := by
    intro value member
    rw [Encoding.framed_length]
    rcases List.mem_append.mp member with member|last
    · obtain ⟨node,nodeMember,rfl⟩ := List.mem_map.mp member
      have belongs : node∈nodes := (List.mem_filter.mp nodeMember).1
      have bound := AnchorCoefficient.coefficient_word_length node query
      have encoded := (node_length_mem nodes node belongs).trans inputBound
      omega
    · have zero : value=0 := List.mem_singleton.mp last
      subst value
      have length : (Encoding.rational.encode 0).length=5 := rfl
      rw [length]
      omega
  simpa only [List.length_append,List.length_singleton] using
    sequence_length_bound (Encoding.framed Encoding.rational) (values nodes query anchor++[0]) _ bounded

theorem rowBudget_polynomial (nodes : List Executable.Node) (query anchor limit : Nat)
    (inputBound : (Encoding.sequence Encoding.node nodes).length ≤ limit) :
    rowBudget nodes query anchor limit ≤ 300000*(limit+query.size+anchor.size+1)^4 := by
  have count := (nodes_length nodes).trans inputBound
  have selected := values_length nodes query anchor
  have stream := stream_length nodes query anchor limit inputBound
  let size := limit+query.size+anchor.size+1
  have positive : 1 ≤ size := by dsimp only [size];omega
  have countSize : nodes.length ≤ size := by dsimp only [size];omega
  have selectedSize : (values nodes query anchor).length+1 ≤ size := by dsimp only [size];omega
  have limitSize : limit+1 ≤ size := by dsimp only [size];omega
  have streamBound : (Encoding.sequence (Encoding.framed Encoding.rational) (values nodes query anchor++[0])).length ≤
      size*(4000*size+1) := stream.trans (Nat.mul_le_mul selectedSize (by omega))
  have mainBound : nodes.length*(200000*size^3+2) ≤ size*(200000*size^3+2) :=
    Nat.mul_le_mul_right _ countSize
  have squareBound : ((values nodes query anchor).length+1)*((values nodes query anchor).length+2) ≤ size*(size+1) :=
    Nat.mul_le_mul selectedSize (by omega)
  have linear : size ≤ size^4 := Nat.le_self_pow (by decide) _
  have square : size^2 ≤ size^4 := Nat.pow_le_pow_right positive (by decide)
  change rowBudget nodes query anchor limit ≤ 300000*size^4
  unfold rowBudget
  change nodes.length*(200000*size^3+2)+1+1+(66+1+(4*((values nodes query anchor).length+1)*
    ((values nodes query anchor).length+2)+17*((values nodes query anchor).length+1)+
    2*(Encoding.sequence (Encoding.framed Encoding.rational) (values nodes query anchor++[0])).length+20)) ≤ _
  nlinarith only [mainBound,squareBound,streamBound,linear,square,selectedSize,positive]

end Counting.StackMachine.AnchorRow
