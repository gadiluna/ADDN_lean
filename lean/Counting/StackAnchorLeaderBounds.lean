import Counting.StackAnchorLeaderRow
import Counting.StackAnchorRowBounds

namespace Counting.StackMachine.AnchorLeaderRow

theorem values_length (nodes : List Executable.Node) (leaders anchor : Nat) :
    (values nodes leaders anchor).length ≤ nodes.length := by
  simpa only [values,List.length_map,AnchorCoefficient.selectedNodes] using
    List.length_filter_le (fun node=>node.level==anchor) nodes

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

theorem stream_length (nodes : List Executable.Node) (leaders anchor : Nat) :
    (Encoding.sequence (Encoding.framed Encoding.rational) (values nodes leaders anchor++[(leaders:Rat)])).length ≤
      ((values nodes leaders anchor).length+1)*(4*leaders.size+15) := by
  have bounded : ∀ value∈values nodes leaders anchor++[(leaders:Rat)],
      ((Encoding.framed Encoding.rational).encode value).length ≤ 4*leaders.size+15 := by
    intro value member
    rw [Encoding.framed_length]
    rcases List.mem_append.mp member with member|last
    · obtain ⟨node,_,rfl⟩ := List.mem_map.mp member
      have bound := word_length node leaders
      change (Encoding.rational.encode (AnchorLeader.value node)).length ≤ 7 at bound
      omega
    · have equal : value=(leaders:Rat) := List.mem_singleton.mp last
      subst value
      rw [RationalArithmetic.rational_nat_encode]
      simp only [List.length_cons,List.length_append,Encoding.natural_length]
      norm_num
      omega
  simpa only [List.length_append,List.length_singleton] using
    sequence_length_bound (Encoding.framed Encoding.rational) (values nodes leaders anchor++[(leaders:Rat)]) _ bounded

theorem rowBudget_polynomial (nodes : List Executable.Node) (leaders anchor limit : Nat)
    (inputBound : (Encoding.sequence Encoding.node nodes).length ≤ limit) :
    rowBudget nodes leaders anchor limit ≤ 300000*(limit+leaders.size+anchor.size+1)^4 := by
  have count := (AnchorRow.nodes_length nodes).trans inputBound
  have selected := values_length nodes leaders anchor
  have stream := stream_length nodes leaders anchor
  let size := limit+leaders.size+anchor.size+1
  have positive : 1 ≤ size := by dsimp only [size];omega
  have countSize : nodes.length ≤ size := by dsimp only [size];omega
  have selectedSize : (values nodes leaders anchor).length+1 ≤ size := by dsimp only [size];omega
  have leaderSize : leaders.size ≤ size := by dsimp only [size];omega
  have streamBound : (Encoding.sequence (Encoding.framed Encoding.rational) (values nodes leaders anchor++[(leaders:Rat)])).length ≤
      size*(4*size+15) := stream.trans (Nat.mul_le_mul selectedSize (by omega))
  have mainBound : nodes.length*(200000*size^3+2) ≤ size*(200000*size^3+2) :=
    Nat.mul_le_mul_right _ countSize
  have squareBound : ((values nodes leaders anchor).length+1)*((values nodes leaders anchor).length+2) ≤ size*(size+1) :=
    Nat.mul_le_mul selectedSize (by omega)
  have linear : size ≤ size^4 := Nat.le_self_pow (by decide) _
  have square : size^2 ≤ size^4 := Nat.pow_le_pow_right positive (by decide)
  change rowBudget nodes leaders anchor limit ≤ 300000*size^4
  unfold rowBudget
  change nodes.length*(200000*size^3+2)+1+1+(23*leaders.size+69+1+(4*((values nodes leaders anchor).length+1)*
    ((values nodes leaders anchor).length+2)+17*((values nodes leaders anchor).length+1)+
    2*(Encoding.sequence (Encoding.framed Encoding.rational) (values nodes leaders anchor++[(leaders:Rat)])).length+20)) ≤ _
  nlinarith only [mainBound,squareBound,streamBound,linear,square,selectedSize,positive,leaderSize]

theorem row_length (nodes : List Executable.Node) (leaders anchor limit : Nat)
    (inputBound : (Encoding.sequence Encoding.node nodes).length ≤ limit) :
    (Encoding.rationalRow.encode (AnchorCoefficient.leaderRow nodes anchor leaders)).length ≤
      30*(limit+leaders.size+1)^2 := by
  have count := (AnchorRow.nodes_length nodes).trans inputBound
  have selected := values_length nodes leaders anchor
  have stream := stream_length nodes leaders anchor
  have bits : ((values nodes leaders anchor).length+1).size ≤
      (values nodes leaders anchor).length+1 := Nat.size_le.mpr Nat.lt_two_pow_self
  change (Encoding.natural.encode (values nodes leaders anchor++[(leaders:Rat)]).length++
    Encoding.sequence (Encoding.framed Encoding.rational) (values nodes leaders anchor++[(leaders:Rat)])).length ≤ _
  rw [List.length_append,Encoding.natural_length,List.length_append,List.length_singleton]
  let size := limit+leaders.size+1
  have positive : 1 ≤ size := by dsimp only [size];omega
  have width : (values nodes leaders anchor).length+1 ≤ size := by dsimp only [size];omega
  have leaderSize : leaders.size ≤ size := by dsimp only [size];omega
  have streamBound := stream.trans (Nat.mul_le_mul width (show 4*leaders.size+15 ≤ 4*size+15 by omega))
  change _ ≤ 30*size^2
  nlinarith only [streamBound,bits,width,positive]

end Counting.StackMachine.AnchorLeaderRow
