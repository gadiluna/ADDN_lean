import Counting.DagSemanticsLabels
import Counting.DagSemanticsValidityCanonical

/-! Exact specification of the implemented syntax validator. The root is
implicit, as in the explicit-vista input specification. Initial nodes have no incoming round and hence
use the canonical unused degree value zero. At positive levels `degree`
labels the parent edge, including the edge entering the bottom. Sorted
positive sparse incidences and topological indices are serialization
conventions; the remaining conditions are the paper's vista properties. -/
namespace Counting.Executable

def NodeSyntax (vista : Vista) (i : Nat) : Prop :=
  if (vista.node i).level = 0 then
    (vista.node i).parent = none ∧ (vista.node i).degree = 0 ∧ (vista.node i).incoming = []
  else ∃ p, (vista.node i).parent = some p ∧ p < i ∧
    (vista.node p).level + 1 = (vista.node i).level ∧
    (vista.node p).leader = (vista.node i).leader ∧ Sparse (vista.node i).incoming ∧
    ∀ edge ∈ (vista.node i).incoming,
      edge.1 < i ∧ (vista.node edge.1).level + 1 = (vista.node i).level

theorem nodeValid_iff_syntax (vista : Vista) (i : Nat) :
    nodeValid vista i = true ↔ NodeSyntax vista i := by
  by_cases zero : (vista.node i).level = 0
  · simp only [NodeSyntax, nodeValid, zero, beq_self_eq_true, if_true,
      Bool.and_eq_true, Option.isNone_iff_eq_none, beq_iff_eq, List.isEmpty_iff, and_assoc]
  · rw [NodeSyntax, if_neg zero]
    constructor
    · intro checked
      obtain ⟨p, parent, earlier, level, leader, sorted, incoming⟩ := nodeValid_positive vista i checked zero
      exact ⟨p, parent, earlier, level, leader, sparse_of_countsSorted _ sorted, incoming⟩
    · rintro ⟨p, parent, earlier, level, leader, sparse, incoming⟩
      simp only [nodeValid, beq_iff_eq, zero, if_false, parent, Bool.and_eq_true,
        decide_eq_true_eq, List.all_eq_true]
      exact ⟨⟨⟨⟨earlier, level⟩, leader⟩, countsSorted_of_sparse _ sparse⟩, incoming⟩

structure VistaSyntax (vista : Vista) : Prop where
  bottom_inside : vista.bottom < vista.nodes.size
  nodes : ∀ i, i < vista.nodes.size → NodeSyntax vista i
  initial_unique : ∀ i j, i < vista.nodes.size → j < vista.nodes.size →
    (vista.node i).level = 0 → (vista.node j).level = 0 →
    (vista.node i).leader = (vista.node j).leader → i = j
  siblings_unique : ∀ i j p, i < vista.nodes.size → j < vista.nodes.size →
    (vista.node i).parent = some p → (vista.node j).parent = some p →
    (vista.node i).degree = (vista.node j).degree →
    (∀ source, countFrom (vista.node i) source = countFrom (vista.node j) source) → i = j
  bottom_unique : ∀ i, i < vista.nodes.size →
    (vista.node i).level = (vista.node vista.bottom).level → i = vista.bottom
  backward_closure : AllReachable vista

theorem valid_initial_unique (vista : Vista) (valid : vista.valid = true)
    (i j : Nat) (insideI : i < vista.nodes.size) (insideJ : j < vista.nodes.size)
    (levelI : (vista.node i).level = 0) (levelJ : (vista.node j).level = 0)
    (status : (vista.node i).leader = (vista.node j).leader) : i = j :=
  decodeNode_injective vista valid 0 i j insideI insideJ levelI levelJ status

theorem valid_siblings_unique (vista : Vista) (valid : vista.valid = true)
    (i j p : Nat) (insideI : i < vista.nodes.size) (insideJ : j < vista.nodes.size)
    (parentI : (vista.node i).parent = some p) (parentJ : (vista.node j).parent = some p)
    (degree : (vista.node i).degree = (vista.node j).degree)
    (counts : ∀ source, countFrom (vista.node i) source = countFrom (vista.node j) source) : i = j := by
  have nonzero (k : Nat) (inside : k < vista.nodes.size) (parent : (vista.node k).parent = some p) :
      (vista.node k).level ≠ 0 := by
    intro zero
    have noParent := (nodeValid_zero vista k (nodeValid_of_valid vista valid k inside) zero).1
    rw [noParent] at parent
    contradiction
  obtain ⟨pi, piEq, _, levelI, leaderI, sortedI, _⟩ :=
    nodeValid_positive vista i (nodeValid_of_valid vista valid i insideI) (nonzero i insideI parentI)
  obtain ⟨pj, pjEq, _, levelJ, leaderJ, sortedJ, _⟩ :=
    nodeValid_positive vista j (nodeValid_of_valid vista valid j insideJ) (nonzero j insideJ parentJ)
  have eqI : pi = p := Option.some.inj (piEq.symm.trans parentI)
  have eqJ : pj = p := Option.some.inj (pjEq.symm.trans parentJ)
  subst pi pj
  have incoming : (vista.node i).incoming = (vista.node j).incoming := by
    apply sparse_eq_of_counts _ _ (sparse_of_countsSorted _ sortedI) (sparse_of_countsSorted _ sortedJ)
    intro source
    simpa only [countFrom, lookup_eq_bundleCount _ (sparse_of_countsSorted _ sortedI),
      lookup_eq_bundleCount _ (sparse_of_countsSorted _ sortedJ)] using counts source
  exact node_index_injective vista valid i j insideI insideJ
    (node_eq_of_fields _ _ (levelI.symm.trans levelJ) (parentI.trans parentJ.symm)
      (leaderI.symm.trans leaderJ) degree incoming)

theorem valid_bottom_unique (vista : Vista) (valid : vista.valid = true)
    (i : Nat) (inside : i < vista.nodes.size)
    (level : (vista.node i).level = (vista.node vista.bottom).level) : i = vista.bottom := by
  have bottomInside : vista.bottom < vista.nodes.size := by
    simp only [Vista.valid, Bool.and_eq_true, decide_eq_true_eq] at valid
    exact valid.1.1.1
  have visible := stored_history_visible vista valid i inside
  rw [level, levels_self, Finset.mem_singleton] at visible
  exact decodeNode_injective vista valid _ i vista.bottom inside bottomInside level rfl visible

theorem syntax_of_valid (vista : Vista) (valid : vista.valid = true) : VistaSyntax vista := by
  refine ⟨?_, fun i inside => (nodeValid_iff_syntax vista i).mp (nodeValid_of_valid vista valid i inside),
    valid_initial_unique vista valid, valid_siblings_unique vista valid,
    valid_bottom_unique vista valid, allReachable_of_valid vista valid⟩
  simp only [Vista.valid, Bool.and_eq_true, decide_eq_true_eq] at valid
  exact valid.1.1.1

theorem valid_of_syntax (vista : Vista) (properties : VistaSyntax vista) : vista.valid = true := by
  apply valid_of_properties vista properties.bottom_inside
    (fun i inside => (nodeValid_iff_syntax vista i).mpr (properties.nodes i inside)) _ properties.backward_closure
  apply List.nodup_iff_injective_getElem.mpr
  intro i j equal
  have insideI : i.val < vista.nodes.size := by simpa only [Array.length_toList] using i.isLt
  have insideJ : j.val < vista.nodes.size := by simpa only [Array.length_toList] using j.isLt
  have nodeEqual : vista.node i.val = vista.node j.val := by
    simpa only [Vista.node, Array.getElem?_eq_getElem insideI, Array.getElem?_eq_getElem insideJ,
      Option.getD_some, Array.getElem_toList] using equal
  apply Fin.ext
  by_cases zero : (vista.node i.val).level = 0
  · exact properties.initial_unique i.val j.val insideI insideJ zero
      (by rw [← nodeEqual]; exact zero) (congrArg Node.leader nodeEqual)
  · have conditions := properties.nodes i.val insideI
    rw [NodeSyntax, if_neg zero] at conditions
    obtain ⟨p, parent, _⟩ := conditions
    exact properties.siblings_unique i.val j.val p insideI insideJ parent
      (by rw [← nodeEqual]; exact parent) (congrArg Node.degree nodeEqual)
      (fun source => congrArg (fun node => countFrom node source) nodeEqual)

/-- Both directions concern the actual Boolean validator, including its
canonical sparse/topological representation conventions. No realization
or positivity condition on an external leader count is assumed here. -/
theorem valid_iff_syntax (vista : Vista) : vista.valid = true ↔ VistaSyntax vista :=
  ⟨syntax_of_valid vista, valid_of_syntax vista⟩

end Counting.Executable
