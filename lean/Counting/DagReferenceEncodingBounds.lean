import Counting.DagUpdateEncodingBounds
import Counting.PropagationEncodingBounds

namespace Counting.Executable

private theorem pair_sequence_cons (edge : Nat×Nat) (edges : List (Nat×Nat)) :
    (Encoding.sequence (Encoding.product Encoding.natural Encoding.natural) (edge::edges)).length=
      2*edge.1.size+1+(2*edge.2.size+1)+
        (Encoding.sequence (Encoding.product Encoding.natural Encoding.natural) edges).length := by
  change ((Encoding.natural.encode edge.1++Encoding.natural.encode edge.2)++
    Encoding.sequence (Encoding.product Encoding.natural Encoding.natural) edges).length=_
  simp only [List.length_append,Encoding.natural_length]

theorem reindex_encoded_length (mapping : Array Nat) (source initial : List (Nat×Nat)) (width : Nat)
    (bounded : ∀ edge∈source,(mapping[edge.1]?.getD 0).size ≤ width) :
    (Encoding.sequence (Encoding.product Encoding.natural Encoding.natural)
      (source.foldl (fun acc edge=>addCount (mapping[edge.1]?.getD 0) edge.2 acc) initial)).length ≤
      (Encoding.sequence (Encoding.product Encoding.natural Encoding.natural) initial).length+
      (Encoding.sequence (Encoding.product Encoding.natural Encoding.natural) source).length+
        2*source.length*width := by
  induction source generalizing initial with
  | nil => simp [Encoding.sequence]
  | cons edge source ih =>
    have first:=addCount_encoded_length (mapping[edge.1]?.getD 0) edge.2 initial
    have key:=bounded edge (by simp)
    have tail:=ih (addCount (mapping[edge.1]?.getD 0) edge.2 initial)
      (fun next member=>bounded next (by simp [member]))
    simp only [List.foldl_cons,List.length_cons,pair_sequence_cons]
    nlinarith only [first,key,tail,Nat.zero_le edge.1.size]

theorem referenceMap_incoming_encoded_length (mapping : Array Nat) (node : Node) (width : Nat)
    (bounded : ∀ i : Nat,(mapping[i]?.getD 0).size ≤ width) :
    (Encoding.sequence (Encoding.product Encoding.natural Encoding.natural) (referenceMap mapping node).incoming).length ≤
      (Encoding.sequence (Encoding.product Encoding.natural Encoding.natural) node.incoming).length+
        2*node.incoming.length*width := by
  simpa only [referenceMap,Encoding.sequence,List.length_nil,Nat.zero_add] using
    reindex_encoded_length mapping node.incoming [] width (fun edge _=>bounded edge.1)

private theorem successor_bits (n width : Nat) (bounded : n.size ≤ width) :
    (n+1).size ≤ width+1 := by
  have value : n+1 ≤ 2^width := by have := Nat.size_le.mp bounded;omega
  simpa only [Nat.size_pow] using Nat.size_le_size value

private theorem node_length_fields (node : Node) :
    (Encoding.node.encode node).length=
      2*node.level.size+1+(2*(node.parent.map (·+1) |>.getD 0).size+1)+1+
      (2*node.degree.size+1)+(2*node.incoming.length.size+1)+
      (Encoding.sequence (Encoding.product Encoding.natural Encoding.natural) node.incoming).length := by
  simp only [Encoding.node,Encoding.transport,Encoding.nodeFields,Encoding.product,Encoding.optionalNatural,
    Encoding.boolean,Encoding.list,List.length_append,Encoding.natural_length,List.length_cons,List.length_nil]
  omega

/-- Reference rewriting charges only the new binary indices and merging
counts. The other node labels are retained verbatim. -/
theorem referenceMap_encoded_length (mapping : Array Nat) (node : Node) (width : Nat)
    (bounded : ∀ i : Nat,(mapping[i]?.getD 0).size ≤ width) :
    (Encoding.node.encode (referenceMap mapping node)).length ≤
      (Encoding.node.encode node).length+2*width*(node.incoming.length+1)+2 := by
  have incoming:=referenceMap_incoming_encoded_length mapping node width bounded
  have header:=Nat.size_le_size (referenceMap_incoming_length mapping node)
  have parent : ((referenceMap mapping node).parent.map (·+1) |>.getD 0).size ≤ width+1 := by
    cases original : node.parent with
    | none => simp [referenceMap,original]
    | some index =>
      simpa only [referenceMap,original,Option.map_some,Option.getD_some] using
        successor_bits (mapping[index]?.getD 0) width (bounded index)
  rw [node_length_fields,node_length_fields]
  change (2*node.level.size+1)+(2*((referenceMap mapping node).parent.map (·+1) |>.getD 0).size+1)+1+
    (2*node.degree.size+1)+(2*(referenceMap mapping node).incoming.length.size+1)+
    (Encoding.sequence (Encoding.product Encoding.natural Encoding.natural) (referenceMap mapping node).incoming).length ≤ _
  nlinarith only [incoming,header,parent,Nat.zero_le (node.parent.map (·+1) |>.getD 0).size]

theorem referenceMap_encoded_polynomial (mapping : Array Nat) (node : Node) :
    (Encoding.node.encode (referenceMap mapping node)).length ≤
      5*((Encoding.node.encode node).length+((Encoding.array Encoding.natural).encode mapping).length+1)^2 := by
  let A:=(Encoding.node.encode node).length
  let B:=((Encoding.array Encoding.natural).encode mapping).length
  have result:=referenceMap_encoded_length mapping node B (Encoding.naturalArray_entry_size_le mapping)
  have edges:=incoming_length_le_bits node.incoming
  have source : node.incoming.length ≤ A := by
    dsimp only [A]
    rw [node_length_fields]
    omega
  have raised:=Nat.mul_le_mul_left (2*B) (Nat.add_le_add_right source 1)
  change _ ≤ 5*(A+B+1)^2
  change _ ≤ A+2*B*(node.incoming.length+1)+2 at result
  nlinarith only [result,raised,Nat.zero_le A,Nat.zero_le B]

end Counting.Executable
