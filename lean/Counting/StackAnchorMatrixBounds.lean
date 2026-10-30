import Counting.StackAnchorMatrixLoop

namespace Counting.StackMachine.AnchorMatrix

theorem flowRow_length (nodes : List Executable.Node) (query anchor limit : Nat)
    (inputBound : (Encoding.sequence Encoding.node nodes).length ≤ limit) :
    (Encoding.rationalRow.encode (AnchorCoefficient.flowRow nodes anchor query)).length ≤ 5000*(limit+1)^2 := by
  have count := (AnchorRow.nodes_length nodes).trans inputBound
  have selected := AnchorRow.values_length nodes query anchor
  have stream := AnchorRow.stream_length nodes query anchor limit inputBound
  have width : (AnchorRow.values nodes query anchor).length+1 ≤ limit+1 := by omega
  have bitCount : ((AnchorRow.values nodes query anchor).length+1).size ≤
      (AnchorRow.values nodes query anchor).length+1 := Nat.size_le.mpr Nat.lt_two_pow_self
  change (Encoding.natural.encode (AnchorRow.values nodes query anchor++[0]).length++
    Encoding.sequence (Encoding.framed Encoding.rational) (AnchorRow.values nodes query anchor++[0])).length ≤ _
  rw [List.length_append,Encoding.natural_length,List.length_append,List.length_singleton]
  have streamBound := stream.trans (Nat.mul_le_mul_right _ width)
  nlinarith

theorem stepBudget_polynomial (nodes : List Executable.Node) (node : Executable.Node)
    (query anchor previous limit : Nat) (tail suffix : List Bool)
    (tableBound : (Encoding.sequence Encoding.node nodes++suffix).length ≤ limit)
    (inputBound : (Encoding.node.encode node++tail).length ≤ limit) (queryBound : query ≤ limit) :
    stepBudget nodes node query anchor previous tail suffix ≤
      8000000*(limit+anchor.size+previous.size+1)^4 := by
  have table : (Encoding.sequence Encoding.node nodes).length ≤ limit := by
    simp only [List.length_append] at tableBound;omega
  have count := (AnchorRow.nodes_length nodes).trans table
  have word := AnchorCoefficient.coefficient_word_length node query
  have result := flowRow_length nodes query anchor limit table
  have rowCost := AnchorRow.rowBudget_polynomial nodes query anchor
    (Encoding.sequence Encoding.node nodes++suffix).length (by simp only [List.length_append];omega)
  have queryBits : query.size ≤ limit := (Nat.size_le.mpr Nat.lt_two_pow_self).trans queryBound
  have level : node.level.size ≤ (Encoding.node.encode node).length := by
    rw [Encoding.node_length];unfold Encoding.nodeBits;omega
  let size := limit+anchor.size+previous.size+1
  have one : 1 ≤ size := by dsimp only [size];omega
  have limitSize : limit+1 ≤ size := by dsimp only [size];omega
  have base : (Encoding.node.encode node++tail).length+query.size+1 ≤ 2*size := by dsimp only [size];omega
  have rowBase : (Encoding.sequence Encoding.node nodes++suffix).length+query.size+anchor.size+1 ≤ 2*size := by
    dsimp only [size];omega
  have rowRaised : AnchorRow.rowBudget nodes query anchor (Encoding.sequence Encoding.node nodes++suffix).length ≤
      4800000*size^4 := by
    have bound := rowCost.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left rowBase 4))
    nlinarith only [bound]
  have readRaised : 100000*((Encoding.node.encode node++tail).length+query.size+1)^3 ≤ 800000*size^3 := by
    have bound := Nat.mul_le_mul_left 100000 (Nat.pow_le_pow_left base 3)
    nlinarith only [bound]
  have resultRaised : (Encoding.rationalRow.encode (AnchorCoefficient.flowRow nodes anchor query)).length ≤ 5000*size^2 :=
    result.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left limitSize 2))
  have linear : size ≤ size^4 := Nat.le_self_pow (by decide) _
  have square : size^2 ≤ size^4 := Nat.pow_le_pow_right one (by decide)
  have cubic : size^3 ≤ size^4 := Nat.pow_le_pow_right one (by decide)
  have wordBound : (AnchorRow.word node query).length ≤ 2000*size := by
    change (AnchorRow.word node query).length ≤ 2000*((Encoding.node.encode node).length+1) at word
    exact word.trans (by simp only [List.length_append] at inputBound;dsimp only [size];omega)
  have tailBound : tail.length ≤ size := by simp only [List.length_append] at inputBound;dsimp only [size];omega
  have suffixBound : suffix.length ≤ size := by simp only [List.length_append] at tableBound;dsimp only [size];omega
  have levelBound : node.level.size ≤ size := by simp only [List.length_append] at inputBound;dsimp only [size];omega
  have previousBound : previous.size ≤ size := by dsimp only [size];omega
  have querySize : query.size ≤ size := by dsimp only [size];omega
  have tableSize : (Encoding.sequence Encoding.node nodes++suffix).length ≤ size := by dsimp only [size];omega
  have countSize : nodes.length ≤ size := by dsimp only [size];omega
  unfold stepBudget flowBudget
  change _ ≤ 8000000*size^4
  omega


theorem loopBudget_uniform (nodes remaining : List Executable.Node) (start anchor previous limit : Nat)
    (suffix : List Bool)
    (tableBound : (Encoding.sequence Encoding.node nodes++suffix).length ≤ limit)
    (remainingBound : (Encoding.sequence Encoding.node remaining++suffix).length ≤ limit)
    (indexBound : start+remaining.length ≤ limit) :
    loopBudget nodes anchor previous suffix start remaining ≤
      remaining.length*(8000000*(limit+anchor.size+previous.size+1)^4+2)+1 := by
  induction remaining generalizing start with
  | nil => simp [loopBudget]
  | cons node rest ih =>
    have step := stepBudget_polynomial nodes node start anchor previous limit
      (Encoding.sequence Encoding.node rest++suffix) suffix tableBound
      (by simpa only [Encoding.sequence,List.append_assoc] using remainingBound) (by simp only [List.length_cons] at indexBound;omega)
    have nextBound : (Encoding.sequence Encoding.node rest++suffix).length ≤ limit := by
      simp only [Encoding.sequence,List.length_append] at remainingBound ⊢;omega
    have nextIndex : start+1+rest.length ≤ limit := by simp only [List.length_cons] at indexBound;omega
    have tail := ih (start+1) nextBound nextIndex
    simp only [loopBudget,List.length_cons]
    nlinarith only [step,tail]

theorem loopBudget_polynomial (nodes : List Executable.Node) (anchor previous limit : Nat) (suffix : List Bool)
    (tableBound : (Encoding.sequence Encoding.node nodes++suffix).length ≤ limit) :
    loopBudget nodes anchor previous suffix 0 nodes ≤ 9000000*(limit+anchor.size+previous.size+1)^5 := by
  have count : nodes.length ≤ limit := by
    have bounded := AnchorRow.nodes_length nodes
    simp only [List.length_append] at tableBound;omega
  have bounded := loopBudget_uniform nodes nodes 0 anchor previous limit suffix tableBound tableBound (by omega)
  let size := limit+anchor.size+previous.size+1
  have countSize : nodes.length ≤ size := by dsimp only [size];omega
  have one : 1 ≤ size := by dsimp only [size];omega
  have raised := bounded.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ countSize) 1)
  have linear : size ≤ size^5 := Nat.le_self_pow (by decide) _
  change _ ≤ 9000000*size^5
  change loopBudget nodes anchor previous suffix 0 nodes ≤ size*(8000000*size^4+2)+1 at raised
  nlinarith only [raised,linear,one]

end Counting.StackMachine.AnchorMatrix
