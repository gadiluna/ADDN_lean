import Counting.EncodingBinary
import Counting.Executable

/-! A fully invertible binary codec for the actual shared DAG representation.
All natural fields, including multiplicities, use binary self-delimiting
codes. Encoding never unfolds a DAG into a history tree. -/
namespace Counting.Encoding

def optionalNatural : Codec (Option Nat) :=
  transport natural (fun value => value.map (· + 1) |>.getD 0)
    (fun n => match n with | 0 => none | n + 1 => some n)
    (by intro value; cases value <;> rfl)

abbrev NodeFields := Nat × Option Nat × Bool × Nat × List (Nat × Nat)

def nodeFields : Codec NodeFields :=
  product natural (product optionalNatural (product boolean (product natural (list (product natural natural)))))

def node : Codec Executable.Node :=
  transport nodeFields
    (fun n => (n.level, n.parent, n.leader, n.degree, n.incoming))
    (fun fields => ⟨fields.1, fields.2.1, fields.2.2.1, fields.2.2.2.1, fields.2.2.2.2⟩)
    (by intro value; rfl)

def vista : Codec Executable.Vista :=
  transport (product (list node) natural)
    (fun v => (v.nodes.toList, v.bottom))
    (fun fields => ⟨fields.1.toArray, fields.2⟩)
    (by intro value; cases value; simp)

theorem node_roundtrip (n : Executable.Node) (suffix : List Bool) :
    node.decode (node.encode n ++ suffix) = some (n, suffix) := node.roundtrip n suffix

theorem vista_roundtrip (v : Executable.Vista) (suffix : List Bool) :
    vista.decode (vista.encode v ++ suffix) = some (v, suffix) := vista.roundtrip v suffix

theorem vista_injective : Function.Injective vista.encode := vista.injective

def nodeBits (n : Executable.Node) : Nat :=
  (2 * n.level.size + 1) +
  (2 * (n.parent.map (· + 1) |>.getD 0).size + 1) +
  1 + (2 * n.degree.size + 1) + (2 * n.incoming.length.size + 1) +
  (n.incoming.map (fun edge => (2 * edge.1.size + 1) + (2 * edge.2.size + 1))).sum

theorem node_length (n : Executable.Node) : (node.encode n).length = nodeBits n := by
  simp only [node, transport, nodeFields, product, List.length_append,
    natural_length, optionalNatural, boolean, List.length_cons, List.length_nil, list_length,
    nodeBits]
  omega

theorem vista_length (v : Executable.Vista) :
    (vista.encode v).length = 2 * v.nodes.size.size + 1 +
      (v.nodes.toList.map nodeBits).sum + (2 * v.bottom.size + 1) := by
  simp only [vista, transport, product, List.length_append, list_length, natural_length,
    Array.length_toList, node_length]

/-- A verifier input includes the actual DAG, one binary count per node,
the number of leaders, and the proposed realization order. -/
def verifierInput : Codec (Executable.Vista × List Nat × Nat × Nat) :=
  product vista (product (list natural) (product natural natural))

theorem verifierInput_length (v : Executable.Vista) (counts : List Nat) (ell order : Nat) :
    (verifierInput.encode (v, counts, ell, order)).length =
      (vista.encode v).length + (2 * counts.length.size + 1 +
        (counts.map (fun n => 2 * n.size + 1)).sum) +
      (2 * ell.size + 1) + (2 * order.size + 1) := by
  simp only [verifierInput, product, List.length_append, list_length, natural_length]
  omega

theorem verifierInput_counts_bound (v : Executable.Vista) (counts : List Nat) (ell order : Nat)
    (bounded : ∀ count ∈ counts, count ≤ order) :
    (verifierInput.encode (v, counts, ell, order)).length ≤
      (vista.encode v).length + (2 * counts.length.size + 1 +
        counts.length * (2 * order.size + 1)) +
      (2 * ell.size + 1) + (2 * order.size + 1) := by
  have bound := natural_list_length_le counts order bounded
  simp only [verifierInput, product, List.length_append, natural_length]
  omega

end Counting.Encoding
