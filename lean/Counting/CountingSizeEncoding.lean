import Counting.LabelBoundsBits
import Counting.EncodingDag

namespace Counting.Encoding
open Executable

/-- Uniform bit bounds on the fields give an exact-codec bound, including
length prefixes and the leader bit. -/
theorem nodeBits_le_uniform (node : Executable.Node) (L n : Nat)
    (level : node.level.size ≤ L)
    (parent : (node.parent.map (·+1) |>.getD 0).size ≤ L)
    (degree : node.degree.size ≤ L)
    (lengthBits : node.incoming.length.size ≤ L)
    (length : node.incoming.length ≤ n)
    (edges : ∀ edge ∈ node.incoming, edge.1.size ≤ L ∧ edge.2.size ≤ L) :
    nodeBits node ≤ 8*L+5+n*(4*L+2) := by
  have edgeSum := List.sum_le_sum (l := node.incoming)
    (f := fun edge => (2*edge.1.size+1)+(2*edge.2.size+1)) (g := fun _ => 4*L+2)
    (fun edge member => by obtain ⟨first, second⟩ := edges edge member; omega)
  simp only [List.map_const', List.sum_replicate, smul_eq_mul] at edgeSum
  have count := Nat.mul_le_mul_right (4*L+2) length
  unfold nodeBits
  omega

/-- Generic upper bound for the implemented binary DAG codec. -/
theorem vista_length_le_uniform (v : Vista) (K E : Nat)
    (nodes : v.nodes.size ≤ K) (bottom : v.bottom ≤ K)
    (nodeBound : ∀ i, i < v.nodes.size → nodeBits (v.node i) ≤ E) :
    (vista.encode v).length ≤ K*(E+4)+2 := by
  have sizeBits : v.nodes.size.size ≤ K :=
    (Nat.size_le.mpr Nat.lt_two_pow_self).trans nodes
  have bottomBits : v.bottom.size ≤ K :=
    (Nat.size_le.mpr Nat.lt_two_pow_self).trans bottom
  have all : ∀ node ∈ v.nodes.toList, nodeBits node ≤ E := by
    intro node member
    obtain ⟨i, within, equal⟩ := List.mem_iff_getElem.mp member
    have inside : i < v.nodes.size := by simpa only [Array.length_toList] using within
    have eq : v.node i = node := by
      simpa only [Array.getElem_toList inside, Vista.node, Array.getElem?_eq_getElem inside,
        Option.getD_some] using equal
    exact eq ▸ nodeBound i inside
  have sum := List.sum_le_sum (l := v.nodes.toList) (f := nodeBits) (g := fun _ => E) all
  simp only [List.map_const', List.sum_replicate, Array.length_toList, smul_eq_mul] at sum
  have count := Nat.mul_le_mul_right E nodes
  rw [vista_length]
  nlinarith

variable {V : Type} [Fintype V]
variable (G : Nat → V → V → Nat) (leader : V → Bool)

/-- Every field, including local DAG references and binary multiplicities,
has a polynomial bit bound in n,t and the maximal label length. -/
theorem physical_nodeBits_le (t : Nat) (observer : V) (v : Vista)
    (valid : v.valid = true) (depth : (v.node v.bottom).level = t)
    (physical : decodeNode v t v.bottom = Counting.history G leader t observer)
    (M : Nat) (mass : ∀ r, 0 < r → r ≤ t → arcMass G r ≤ M)
    (i : Nat) (inside : i < v.nodes.size) :
    let L := t+(t+1)*Fintype.card V+Nat.size M+Fintype.card V+1
    nodeBits (v.node i) ≤ 8*L+5+Fintype.card V*(4*L+2) := by
  dsimp only
  let L := t+(t+1)*Fintype.card V+Nat.size M+Fintype.card V+1
  have nodeCount := nodes_size_le_depth_mul_card G leader t observer v valid depth physical
  have label := stored_labels_le G leader t observer v valid depth physical M mass i inside
  have incLength := incoming_length_le_card G leader t observer v valid depth physical i inside
  have storedLevel := stored_level_le_bottom v valid i inside
  have levelBits : (v.node i).level.size ≤ L :=
    (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by dsimp [L]; omega)
  have parentBound : ((v.node i).parent.map (·+1) |>.getD 0) ≤ v.nodes.size := by
    by_cases zero : (v.node i).level = 0
    · rw [(nodeValid_zero v i (nodeValid_of_valid v valid i inside) zero).1]
      simp
    · obtain ⟨p, hp, smaller, _, _, _, _⟩ := nodeValid_positive v i (nodeValid_of_valid v valid i inside) zero
      simp only [hp, Option.map_some, Option.getD_some]
      omega
  have parentBits : ((v.node i).parent.map (·+1) |>.getD 0).size ≤ L :=
    (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by dsimp [L]; omega)
  have degreeBits : (v.node i).degree.size ≤ L :=
    (Nat.size_le_size label.1).trans (by dsimp [L]; omega)
  have lengthBits : (v.node i).incoming.length.size ≤ L :=
    (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by dsimp [L]; omega)
  apply nodeBits_le_uniform _ L (Fintype.card V) levelBits parentBits degreeBits lengthBits incLength
  intro edge present
  have reference : edge.1 < v.nodes.size := by
    by_cases zero : (v.node i).level = 0
    · rw [(nodeValid_zero v i (nodeValid_of_valid v valid i inside) zero).2.2] at present
      cases present
    · obtain ⟨_, _, _, _, _, _, incoming⟩ := nodeValid_positive v i (nodeValid_of_valid v valid i inside) zero
      exact (incoming edge present).1.trans inside
  exact ⟨(Nat.size_le.mpr Nat.lt_two_pow_self).trans (by dsimp [L]; omega),
    (Nat.size_le_size (incoming_entry_le_arc_bound G leader t observer v valid depth physical M mass i inside edge present)).trans
      (by dsimp [L]; omega)⟩

/-- Polynomial size of the actual invertible binary encoding in n, depth t,
and B=size(M). No cost bound for generating or manipulating it is asserted. -/
theorem physical_vista_encoding_length (t : Nat) (observer : V) (v : Vista)
    (valid : v.valid = true) (depth : (v.node v.bottom).level = t)
    (physical : decodeNode v t v.bottom = Counting.history G leader t observer)
    (M : Nat) (mass : ∀ r, 0 < r → r ≤ t → arcMass G r ≤ M) :
    let n := Fintype.card V
    let K := (t+1)*n
    let L := t+K+Nat.size M+n+1
    (vista.encode v).length ≤ K*(8*L+9+n*(4*L+2))+2 := by
  dsimp only
  have nodes := nodes_size_le_depth_mul_card G leader t observer v valid depth physical
  have bottom : v.bottom < v.nodes.size := by
    simp only [Vista.valid, Bool.and_eq_true, decide_eq_true_eq] at valid
    exact valid.1.1.1
  have bound := vista_length_le_uniform v ((t+1)*Fintype.card V)
    (8*(t+(t+1)*Fintype.card V+Nat.size M+Fintype.card V+1)+5+
      Fintype.card V*(4*(t+(t+1)*Fintype.card V+Nat.size M+Fintype.card V+1)+2))
    nodes (bottom.le.trans nodes) (physical_nodeBits_le G leader t observer v valid depth physical M mass)
  convert bound using 1; ring

end Counting.Encoding
