import Counting.DagUpdateSizeBounds
import Counting.EncodingDag

namespace Counting.Executable

theorem addCount_length_le (index count : Nat) (edges : List (Nat×Nat)) :
    (addCount index count edges).length ≤ edges.length+1 := by
  induction edges with
  | nil => simp only [addCount];split <;> simp
  | cons edge edges ih =>
    rcases edge with ⟨key,value⟩
    simp only [addCount]
    split
    · simp
    · split
      · simp
      · split
        · simp
        · simp only [List.length_cons];omega

theorem addCount_mass (index count : Nat) (edges : List (Nat×Nat)) :
    ((addCount index count edges).map Prod.snd).sum=(edges.map Prod.snd).sum+count := by
  induction edges with
  | nil => by_cases zero : count=0 <;> simp [addCount,zero]
  | cons edge edges ih =>
    rcases edge with ⟨key,value⟩
    by_cases zero : count=0
    · simp [addCount,zero]
    · simp only [addCount,show (count==0)=false by simp [zero],Bool.false_eq_true,if_false]
      split
      · simp [Nat.add_assoc,Nat.add_comm]
      · split
        · simp [Nat.add_comm]
        · simp [ih,Nat.add_assoc]

theorem reindex_length_le (mapping : Array Nat) (source initial : List (Nat×Nat)) :
    (source.foldl (fun acc edge=>addCount (mapping[edge.1]?.getD 0) edge.2 acc) initial).length ≤
      initial.length+source.length := by
  induction source generalizing initial with
  | nil => simp
  | cons edge source ih =>
    have first:=addCount_length_le (mapping[edge.1]?.getD 0) edge.2 initial
    have tail:=ih (addCount (mapping[edge.1]?.getD 0) edge.2 initial)
    simp only [List.foldl_cons,List.length_cons]
    omega

theorem reindex_mass (mapping : Array Nat) (source initial : List (Nat×Nat)) :
    ((source.foldl (fun acc edge=>addCount (mapping[edge.1]?.getD 0) edge.2 acc) initial).map Prod.snd).sum=
      (initial.map Prod.snd).sum+(source.map Prod.snd).sum := by
  induction source generalizing initial with
  | nil => simp
  | cons edge source ih => simp only [List.foldl_cons,ih,addCount_mass,List.map_cons,List.sum_cons,Nat.add_assoc]

theorem referenceMap_incoming_length (mapping : Array Nat) (node : Node) :
    (referenceMap mapping node).incoming.length ≤ node.incoming.length := by
  simpa only [referenceMap,List.length_nil,Nat.zero_add] using reindex_length_le mapping node.incoming []

theorem referenceMap_incoming_mass (mapping : Array Nat) (node : Node) :
    ((referenceMap mapping node).incoming.map Prod.snd).sum=(node.incoming.map Prod.snd).sum := by
  simpa only [referenceMap,List.map_nil,List.sum_nil,Nat.zero_add] using reindex_mass mapping node.incoming []

private theorem nat_add_bits (a b : Nat) : (a+b).size ≤ a.size+b.size+1 := by
  apply Nat.size_le.mpr
  have first : a<2^(a.size+b.size) :=
    (Nat.lt_size_self a).trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  have second : b<2^(a.size+b.size) :=
    (Nat.lt_size_self b).trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  rw [pow_succ]
  omega

private theorem incoming_cons_length (edge : Nat×Nat) (edges : List (Nat×Nat)) :
    (Encoding.sequence (Encoding.product Encoding.natural Encoding.natural) (edge::edges)).length=
      2*edge.1.size+1+(2*edge.2.size+1)+
        (Encoding.sequence (Encoding.product Encoding.natural Encoding.natural) edges).length := by
  change ((Encoding.natural.encode edge.1++Encoding.natural.encode edge.2)++
    Encoding.sequence (Encoding.product Encoding.natural Encoding.natural) edges).length=_
  simp only [List.length_append,Encoding.natural_length]

/-- Actual sparse insertion has additive encoded growth. This holds for
unsorted inputs too, matching the total executable function exactly. -/
theorem addCount_encoded_length (index count : Nat) (edges : List (Nat×Nat)) :
    (Encoding.sequence (Encoding.product Encoding.natural Encoding.natural) (addCount index count edges)).length ≤
      (Encoding.sequence (Encoding.product Encoding.natural Encoding.natural) edges).length+
        2*index.size+2*count.size+2 := by
  induction edges with
  | nil =>
    simp only [addCount]
    split
    · simp [Encoding.sequence]
    · rw [incoming_cons_length];simp [Encoding.sequence];omega
  | cons edge edges ih =>
    rcases edge with ⟨key,value⟩
    have sumBound:=nat_add_bits value count
    simp only [addCount]
    split
    · omega
    · split
      · simp only [incoming_cons_length];omega
      · split
        · simp only [incoming_cons_length];omega
        · simp only [incoming_cons_length];omega

theorem incoming_mass_bits (edges : List (Nat×Nat)) :
    (edges.map Prod.snd).sum.size ≤
      (Encoding.sequence (Encoding.product Encoding.natural Encoding.natural) edges).length := by
  induction edges with
  | nil => simp [Encoding.sequence]
  | cons edge edges ih =>
    have added:=nat_add_bits edge.2 (edges.map Prod.snd).sum
    simp only [List.map_cons,List.sum_cons,Encoding.sequence,List.length_append,
      Encoding.product,Encoding.natural_length] at ih ⊢
    omega

theorem incoming_length_le_bits (edges : List (Nat×Nat)) :
    edges.length ≤
      (Encoding.sequence (Encoding.product Encoding.natural Encoding.natural) edges).length := by
  induction edges with
  | nil => simp [Encoding.sequence]
  | cons edge edges ih =>
    simp only [List.length_cons,Encoding.sequence,Encoding.product,List.length_append,
      Encoding.natural_length] at ih ⊢
    omega

/-- Merging colliding references preserves total multiplicity. Its binary
size is bounded by the original sparse input, even for enormous counts. -/
theorem referenceMap_count_bits (mapping : Array Nat) (node : Node)
    (edge : Nat×Nat) (member : edge∈(referenceMap mapping node).incoming) :
    edge.2.size ≤ (Encoding.node.encode node).length := by
  have term : edge.2 ≤ ((referenceMap mapping node).incoming.map Prod.snd).sum :=
    List.single_le_sum (fun _ _=>Nat.zero_le _) _ (List.mem_map.mpr ⟨edge,member,rfl⟩)
  rw [referenceMap_incoming_mass] at term
  have bits:=(Nat.size_le_size term).trans (incoming_mass_bits node.incoming)
  have sequenceLength :
      (Encoding.sequence (Encoding.product Encoding.natural Encoding.natural) node.incoming).length ≤
        (Encoding.node.encode node).length := by
    simp only [Encoding.node,Encoding.transport,Encoding.nodeFields,Encoding.product,
      Encoding.list,List.length_append]
    omega
  exact bits.trans sequenceLength

end Counting.Executable
