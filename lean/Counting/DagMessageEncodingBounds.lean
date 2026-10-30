import Counting.DagMessageBounds

namespace Counting.Executable

theorem mergeMessages_edges_length (state : MergeState) (messages : List (Vista×Nat)) :
    (messages.foldl mergeMessage state).2.length ≤ state.2.length+messages.length := by
  induction messages generalizing state with
  | nil => simp
  | cons message messages ih =>
    have next := addCount_length_le ((importVista state.1 message.1).2[message.1.bottom]?.getD 0)
      message.2 state.2
    have rest := ih (mergeMessage state message)
    simp only [List.foldl_cons,List.length_cons]
    change (messages.foldl mergeMessage (mergeMessage state message)).2.length ≤
      (addCount ((importVista state.1 message.1).2[message.1.bottom]?.getD 0)
        message.2 state.2).length+messages.length at rest
    omega

/-- A uniform quadratic encoding bound for the entire received-message
fold. It includes both array/list headers, arbitrary initial pools, zero or
large multiplicities, and malformed references with their executable defaults. -/
theorem mergeMessages_encoded_polynomial (state : MergeState) (messages : List (Vista×Nat)) :
    let K := ((Encoding.array Encoding.node).encode state.1).length+
      ((Encoding.list (Encoding.product Encoding.natural Encoding.natural)).encode state.2).length+
      (Encoding.sequence messageEncoding messages).length+1
    ((Encoding.array Encoding.node).encode (messages.foldl mergeMessage state).1).length ≤ 20*K^2 ∧
    ((Encoding.list (Encoding.product Encoding.natural Encoding.natural)).encode
      (messages.foldl mergeMessage state).2).length ≤ 20*K^2 := by
  let P := ((Encoding.array Encoding.node).encode state.1).length
  let E := ((Encoding.list (Encoding.product Encoding.natural Encoding.natural)).encode state.2).length
  let S := (Encoding.sequence messageEncoding messages).length
  let K := P+E+S+1
  let width := state.1.size+messageNodes messages
  let result := messages.foldl mergeMessage state
  have initialCount : state.1.size ≤ P := Encoding.array_size_le_length _ _
    (fun node _=>Encoding.node_positive_length node)
  have nodes := messageNodes_length messages
  have count := message_count_length messages
  have widthBound : width≤K := by dsimp only [width,K,P,E,S] at *;omega
  have payload := mergeMessages_payload_bound state messages width le_rfl
  have poolCount := mergeMessages_size_le state messages
  have poolHeader : result.1.size.size ≤ width :=
    (Nat.size_le.mpr Nat.lt_two_pow_self).trans poolCount
  have initialPayload : (Encoding.sequence Encoding.node state.1.toList).length≤P := by
    simp only [P,Encoding.array,Encoding.transport,Encoding.list,List.length_append]
    omega
  have edgePayload : (Encoding.sequence (Encoding.product Encoding.natural Encoding.natural) state.2).length≤E := by
    simp only [E,Encoding.list,List.length_append]
    omega
  have initialEdgeCount := (incoming_length_le_bits state.2).trans edgePayload
  have edgeCount := mergeMessages_edges_length state messages
  change result.2.length ≤ state.2.length+messages.length at edgeCount
  have edgeHeader : result.2.length.size≤K := by
    have header : result.2.length.size≤result.2.length := Nat.size_le.mpr Nat.lt_two_pow_self
    dsimp only [K,S] at *
    omega
  have positive : 1≤K := by dsimp only [K];omega
  have sK : S≤K := by dsimp only [K];omega
  have pK : P≤K := by dsimp only [K];omega
  have eK : E≤K := by dsimp only [K];omega
  have countK : messages.length≤K := count.trans sK
  have poolScale := Nat.mul_le_mul (show 4*width+6≤4*K+6 by omega) sK
  have edgeScale := Nat.mul_le_mul countK (show 2*width+2≤2*K+2 by omega)
  change ((Encoding.array Encoding.node).encode result.1).length≤20*K^2 ∧
    ((Encoding.list (Encoding.product Encoding.natural Encoding.natural)).encode result.2).length≤20*K^2
  constructor
  · rw [Encoding.array_length,←Encoding.sequence_length]
    have poolBound := payload.1
    change (Encoding.sequence Encoding.node result.1.toList).length ≤
      (Encoding.sequence Encoding.node state.1.toList).length+(4*width+6)*S at poolBound
    nlinarith only [poolHeader,widthBound,poolBound,initialPayload,poolScale,pK,positive]
  · change (Encoding.natural.encode result.2.length++
      Encoding.sequence (Encoding.product Encoding.natural Encoding.natural) result.2).length≤20*K^2
    rw [List.length_append,Encoding.natural_length]
    have edgeBound := payload.2
    change (Encoding.sequence (Encoding.product Encoding.natural Encoding.natural) result.2).length ≤
      (Encoding.sequence (Encoding.product Encoding.natural Encoding.natural) state.2).length+
      messages.length*(2*width+2)+2*S at edgeBound
    nlinarith only [edgeHeader,edgeBound,edgePayload,edgeScale,eK,sK,positive]

theorem message_sequence_prefix_length (visited messages : List (Vista×Nat))
    (before : visited.IsPrefix messages) :
    (Encoding.sequence messageEncoding visited).length≤(Encoding.sequence messageEncoding messages).length := by
  obtain ⟨suffix,rfl⟩ := before
  simp only [Encoding.sequence_length,List.map_append,List.sum_append]
  omega

theorem mergeMessages_prefix_encoded_polynomial (state : MergeState)
    (visited messages : List (Vista×Nat)) (before : visited.IsPrefix messages) :
    let K := ((Encoding.array Encoding.node).encode state.1).length+
      ((Encoding.list (Encoding.product Encoding.natural Encoding.natural)).encode state.2).length+
      (Encoding.sequence messageEncoding messages).length+1
    ((Encoding.array Encoding.node).encode (visited.foldl mergeMessage state).1).length≤20*K^2 ∧
    ((Encoding.list (Encoding.product Encoding.natural Encoding.natural)).encode
      (visited.foldl mergeMessage state).2).length≤20*K^2 := by
  have bounded := mergeMessages_encoded_polynomial state visited
  have shorter := message_sequence_prefix_length visited messages before
  dsimp only at bounded ⊢
  have base := Nat.add_le_add_right (Nat.add_le_add_left shorter
    (((Encoding.array Encoding.node).encode state.1).length+
      ((Encoding.list (Encoding.product Encoding.natural Encoding.natural)).encode state.2).length)) 1
  have power := Nat.mul_le_mul_left 20 (Nat.pow_le_pow_left base 2)
  exact ⟨bounded.1.trans power,bounded.2.trans power⟩

end Counting.Executable
