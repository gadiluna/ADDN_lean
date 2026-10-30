import Counting.DagSemanticsClosure
import Counting.DagSemanticsUpdate

namespace Counting.Executable

theorem countsSorted_of_sparse (bundles : List (Nat × Nat)) (sparse : Sparse bundles) :
    countsSorted bundles = true := by
  induction bundles with
  | nil => rfl
  | cons edge rest ih =>
      have tail := sparse_tail edge rest sparse
      simp only [countsSorted, Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨⟨sparse.2 edge (by simp), ?_⟩, ih tail⟩
      cases rest with
      | nil => rfl
      | cons next rest =>
          simpa only [List.head?_cons, Option.map_some, Option.getD_some, decide_eq_true_eq] using
            (List.pairwise_cons.mp sparse.1).1 next (by simp)

theorem sparse_addCount (index count : Nat) (bundles : List (Nat × Nat))
    (sparse : Sparse bundles) : Sparse (addCount index count bundles) := by
  induction bundles with
  | nil =>
      by_cases hc : count = 0
      · simp [addCount, hc, Sparse]
      · simp [addCount, hc, Sparse, Nat.pos_of_ne_zero hc]
  | cons edge rest ih =>
      rcases edge with ⟨i, c⟩
      have tail := sparse_tail (i, c) rest sparse
      have first := (List.pairwise_cons.mp sparse.1).1
      have positive := sparse.2 (i, c) (by simp)
      by_cases hc : count = 0
      · simpa only [addCount, beq_iff_eq, hc, if_true] using sparse
      by_cases hi : index = i
      · subst i
        simp only [addCount, beq_iff_eq, hc, if_false, if_true]
        exact ⟨List.pairwise_cons.mpr ⟨first, tail.1⟩,
          by intro e he; rcases List.mem_cons.mp he with rfl | he
             · omega
             · exact tail.2 e he⟩
      by_cases hlt : index < i
      · simp only [addCount, beq_iff_eq, hc, hi, hlt, if_false, if_true]
        refine ⟨List.pairwise_cons.mpr ⟨?_, sparse.1⟩, ?_⟩
        · intro e he
          rcases List.mem_cons.mp he with rfl | he
          · exact hlt
          · exact hlt.trans (first e he)
        · intro e he
          rcases List.mem_cons.mp he with rfl | he
          · exact Nat.pos_of_ne_zero hc
          · exact sparse.2 e he
      · simp only [addCount, beq_iff_eq, hc, hi, hlt, if_false]
        have next := ih tail
        refine ⟨List.pairwise_cons.mpr ⟨?_, next.1⟩, ?_⟩
        · exact bundleKeys_addCount (fun key => i < key) index count rest (by omega) first
        · intro e he
          rcases List.mem_cons.mp he with rfl | he
          · exact positive
          · exact next.2 e he

theorem sparse_reindex (mapping : Array Nat) (bundles accumulated : List (Nat × Nat))
    (sparse : Sparse accumulated) :
    Sparse (bundles.foldl
      (fun acc edge => addCount (mapping[edge.1]?.getD 0) edge.2 acc) accumulated) := by
  induction bundles generalizing accumulated with
  | nil => exact sparse
  | cons edge rest ih => exact ih _ (sparse_addCount _ _ _ sparse)

theorem referenceMap_countsSorted (mapping : Array Nat) (node : Node) :
    countsSorted (referenceMap mapping node).incoming = true :=
  countsSorted_of_sparse _ (sparse_reindex mapping node.incoming [] (by simp [Sparse]))

/-- A full local node check before appending to the shared pool. -/
def NodeReady (vista : Vista) (node : Node) : Prop :=
  (node.level = 0 ∧ node.parent = none ∧ node.degree = 0 ∧ node.incoming = []) ∨
  (node.level ≠ 0 ∧ ∃ p, node.parent = some p ∧ p < vista.nodes.size ∧
    (vista.node p).level + 1 = node.level ∧ (vista.node p).leader = node.leader ∧
    countsSorted node.incoming = true ∧ ∀ edge ∈ node.incoming,
      edge.1 < vista.nodes.size ∧ (vista.node edge.1).level + 1 = node.level)

def NodesValid (vista : Vista) : Prop :=
  ∀ i, i < vista.nodes.size → nodeValid vista i = true

theorem nodesValid_of_valid (vista : Vista) (valid : vista.valid = true) : NodesValid vista :=
  nodeValid_of_valid vista valid

theorem nodeReady_of_check (vista : Vista) (i : Nat) (inside : i < vista.nodes.size)
    (valid : nodeValid vista i = true) : NodeReady vista (vista.node i) := by
  by_cases zero : (vista.node i).level = 0
  · exact Or.inl ⟨zero, nodeValid_zero vista i valid zero⟩
  · obtain ⟨p, hp, hpi, level, leader, counts, incoming⟩ := nodeValid_positive vista i valid zero
    exact Or.inr ⟨zero, p, hp, hpi.trans inside, level, leader, counts,
      fun e he => ⟨(incoming e he).1.trans inside, (incoming e he).2⟩⟩

theorem nodeValid_of_fields (vista : Vista) (i : Nat)
    (fields : (vista.node i).level = 0 ∧ (vista.node i).parent = none ∧
        (vista.node i).degree = 0 ∧ (vista.node i).incoming = [] ∨
      (vista.node i).level ≠ 0 ∧ ∃ p, (vista.node i).parent = some p ∧ p < i ∧
        (vista.node p).level + 1 = (vista.node i).level ∧
        (vista.node p).leader = (vista.node i).leader ∧
        countsSorted (vista.node i).incoming = true ∧ ∀ e ∈ (vista.node i).incoming,
          e.1 < i ∧ (vista.node e.1).level + 1 = (vista.node i).level) :
    nodeValid vista i = true := by
  rcases fields with ⟨zero, parent, degree, incoming⟩ | ⟨positive, p, parent, bound, level, leader, counts, incoming⟩
  · simp [nodeValid, zero, parent, degree, incoming]
  · simp only [nodeValid, beq_iff_eq, positive, if_false, parent, Bool.and_eq_true,
      decide_eq_true_eq, counts, and_true]
    exact ⟨⟨⟨bound, level⟩, leader⟩,
      List.all_eq_true.mpr (by intro e he; simpa using incoming e he)⟩

theorem nodeValid_of_extends (source target : Vista) (extension : Extends source target)
    (i : Nat) (inside : i < source.nodes.size) (valid : nodeValid source i = true) :
    nodeValid target i = true := by
  apply nodeValid_of_fields
  rw [extension i inside]
  by_cases zero : (source.node i).level = 0
  · exact Or.inl ⟨zero, nodeValid_zero source i valid zero⟩
  · obtain ⟨p, hp, hpi, level, leader, counts, incoming⟩ := nodeValid_positive source i valid zero
    refine Or.inr ⟨zero, p, hp, hpi, ?_, ?_, counts, ?_⟩
    · simpa only [extension p (hpi.trans inside)] using level
    · simpa only [extension p (hpi.trans inside)] using leader
    · intro e he
      obtain ⟨hei, hel⟩ := incoming e he
      exact ⟨hei, by simpa only [extension e.1 (hei.trans inside)] using hel⟩

theorem nodesValid_push (vista : Vista) (node : Node)
    (valid : NodesValid vista) (ready : NodeReady vista node) :
    NodesValid ⟨vista.nodes.push node, vista.bottom⟩ := by
  intro i hi
  have le : i ≤ vista.nodes.size := Nat.le_of_lt_succ (by simpa only [Array.size_push] using hi)
  rcases lt_or_eq_of_le le with inside | rfl
  · exact nodeValid_of_extends vista _ (fun j hj => node_push_old _ _ _ _ hj) i inside (valid i inside)
  · apply nodeValid_of_fields
    rw [node_push_last]
    rcases ready with zero | ⟨positive, p, hp, bound, level, leader, counts, incoming⟩
    · exact Or.inl zero
    · exact Or.inr ⟨positive, p, hp, bound,
        by simpa only [node_push_old _ _ _ _ bound] using level,
        by simpa only [node_push_old _ _ _ _ bound] using leader,
        counts, fun e he => ⟨(incoming e he).1,
          by simpa only [node_push_old _ _ _ _ (incoming e he).1] using (incoming e he).2⟩⟩

theorem intern_nodesValid (nodes : Array Node) (node : Node)
    (valid : NodesValid ⟨nodes, 0⟩) (ready : NodeReady ⟨nodes, 0⟩ node) :
    NodesValid ⟨(intern nodes node).1, 0⟩ := by
  unfold intern
  split
  · exact valid
  · exact nodesValid_push ⟨nodes, 0⟩ node valid ready

theorem referenceMap_nodeReady (source target : Vista) (mapping : Array Nat) (node : Node)
    (ready : NodeReady source node) (relabels : Relabels source target mapping)
    (bounded : ∀ i, i < source.nodes.size → mapping[i]?.getD 0 < target.nodes.size) :
    NodeReady target (referenceMap mapping node) := by
  have fields (i : Nat) (hi : i < source.nodes.size) :
      (target.node (mapping[i]?.getD 0)).level = (source.node i).level ∧
      (target.node (mapping[i]?.getD 0)).leader = (source.node i).leader := by
    rw [relabels i hi]
    exact ⟨rfl, rfl⟩
  rcases ready with ⟨zero, parent, degree, incoming⟩ | ⟨positive, p, hp, bound, level, leader, _, incoming⟩
  · left
    simp only [referenceMap, zero, parent, degree, incoming, Option.map_none, List.foldl_nil, and_self]
  · right
    refine ⟨positive, mapping[p]?.getD 0, by simp only [referenceMap, hp, Option.map_some],
      bounded p bound, ?_, ?_, referenceMap_countsSorted mapping node, ?_⟩
    · exact (congrArg (· + 1) (fields p bound).1).trans level
    · exact (fields p bound).2.trans leader
    · apply referenceMap_keys (fun i => i < target.nodes.size ∧ (target.node i).level + 1 = node.level)
      intro e he
      exact ⟨bounded e.1 (incoming e he).1,
        (congrArg (· + 1) (fields e.1 (incoming e he).1).1).trans (incoming e he).2⟩

theorem intern_nodup (nodes : Array Node) (node : Node) (distinct : nodes.toList.Nodup) :
    (intern nodes node).1.toList.Nodup := by
  unfold intern
  split
  · exact distinct
  · rename_i absent
    rw [Array.toList_push, List.nodup_append]
    refine ⟨distinct, by simp, ?_⟩
    intro x hx y hy
    simp only [List.mem_singleton] at hy
    subst y
    intro equal
    subst x
    obtain ⟨i, hi, equal⟩ := Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp hx)
    have no := List.find?_eq_none.mp absent i (List.mem_range.mpr hi)
    simp only [Array.getElem?_eq_getElem hi, Option.getD_some, equal, beq_self_eq_true] at no
    contradiction

theorem nodesValid_topological (vista : Vista) (valid : NodesValid vista) : Topological vista := by
  intro i hi
  by_cases zero : (vista.node i).level = 0
  · obtain ⟨parent, _, incoming⟩ := nodeValid_zero vista i (valid i hi) zero
    exact ⟨by intro p hp; rw [parent] at hp; contradiction,
      by intro e he; rw [incoming] at he; contradiction⟩
  · obtain ⟨p, hp, bound, _, _, _, incoming⟩ := nodeValid_positive vista i (valid i hi) zero
    exact ⟨by intro q hq; have eq := Option.some.inj (hp.symm.trans hq); simpa only [← eq] using bound,
      fun e he => (incoming e he).1⟩

theorem nodesValid_references (vista : Vista) (valid : NodesValid vista)
    (i : Nat) (hi : i < vista.nodes.size) :
    ReferencesIn (vista.node i) (lowerNodes vista (vista.node i).level) := by
  by_cases zero : (vista.node i).level = 0
  · obtain ⟨parent, _, incoming⟩ := nodeValid_zero vista i (valid i hi) zero
    exact ⟨by intro p hp; rw [parent] at hp; contradiction,
      by intro e he; rw [incoming] at he; contradiction⟩
  · obtain ⟨p, hp, bound, level, _, _, incoming⟩ := nodeValid_positive vista i (valid i hi) zero
    constructor
    · intro q hq
      have eq := Option.some.inj (hp.symm.trans hq)
      subst q
      exact (mem_lowerNodes _ _ _).mpr ⟨bound.trans hi, by omega⟩
    · intro e he
      obtain ⟨bound, level⟩ := incoming e he
      exact (mem_lowerNodes _ _ _).mpr ⟨bound.trans hi, by omega⟩


theorem nodesValid_of_push (nodes : Array Node) (node : Node) (bottom : Nat)
    (valid : NodesValid ⟨nodes.push node, bottom⟩) :
    NodesValid ⟨nodes, bottom⟩ ∧ NodeReady ⟨nodes, bottom⟩ node := by
  have check (i : Nat) (inside : i < nodes.size) : nodeValid ⟨nodes, bottom⟩ i = true := by
    have hi : i < (nodes.push node).size := by simp only [Array.size_push]; omega
    have current := valid i hi
    by_cases zero : ((Vista.mk (nodes.push node) bottom).node i).level = 0
    · have fields := nodeValid_zero _ i current zero
      apply nodeValid_of_fields
      left
      simpa only [node_push_old _ _ _ _ inside] using And.intro zero fields
    · obtain ⟨p, hp, bound, level, leader, counts, incoming⟩ := nodeValid_positive _ i current zero
      apply nodeValid_of_fields
      rw [node_push_old _ _ _ _ inside] at zero hp level leader counts incoming
      right
      exact ⟨zero, p, hp, bound,
        by simpa only [node_push_old _ _ _ _ (bound.trans inside)] using level,
        by simpa only [node_push_old _ _ _ _ (bound.trans inside)] using leader,
        counts, fun e he => ⟨(incoming e he).1,
          by simpa only [node_push_old _ _ _ _ ((incoming e he).1.trans inside)] using (incoming e he).2⟩⟩
  refine ⟨check, ?_⟩
  have current := valid nodes.size (by simp)
  by_cases zero : node.level = 0
  · have fields := nodeValid_zero _ nodes.size current (by simpa only [node_push_last] using zero)
    exact Or.inl ⟨zero, by simpa only [node_push_last] using fields⟩
  · obtain ⟨p, hp, bound, level, leader, counts, incoming⟩ :=
      nodeValid_positive _ nodes.size current (by simpa only [node_push_last] using zero)
    simp only [node_push_last] at hp level leader counts incoming
    exact Or.inr ⟨zero, p, hp, bound,
      by simpa only [node_push_old _ _ _ _ bound] using level,
      by simpa only [node_push_old _ _ _ _ bound] using leader,
      counts, fun e he => ⟨(incoming e he).1,
        by simpa only [node_push_old _ _ _ _ (incoming e he).1] using (incoming e he).2⟩⟩

theorem importVista_nodesValid (pool : Array Node) (source : Vista)
    (poolValid : NodesValid ⟨pool, 0⟩) (sourceValid : NodesValid source) :
    NodesValid ⟨(importVista pool source).1, 0⟩ := by
  rcases source with ⟨⟨nodes⟩, bottom⟩
  induction nodes using List.reverseRecOn with
  | nil => exact poolValid
  | append_singleton nodes node ih =>
      let previous : Vista := ⟨⟨nodes⟩, bottom⟩
      have pushed : (⟨nodes ++ [node]⟩ : Array Node) = previous.nodes.push node := by
        apply Array.ext'
        simp [previous]
      rw [pushed] at sourceValid ⊢
      obtain ⟨oldValid, ready⟩ := nodesValid_of_push _ _ _ sourceValid
      have beforeCorrect := importVista_correct pool previous (nodesValid_topological _ oldValid)
      rw [importVista_push]
      exact intern_nodesValid _ _ (ih oldValid)
        (referenceMap_nodeReady previous _ _ node ready beforeCorrect.2.2.2 beforeCorrect.2.2.1)

theorem importVista_nodup (pool : Array Node) (source : Vista) (distinct : pool.toList.Nodup) :
    (importVista pool source).1.toList.Nodup := by
  have fold (nodes : List Node) (state : Array Node × Array Nat) (h : state.1.toList.Nodup) :
      (nodes.foldl (fun state node =>
        let next := intern state.1 (referenceMap state.2 node)
        (next.1, state.2.push next.2)) state).1.toList.Nodup := by
    induction nodes generalizing state with
    | nil => exact h
    | cons node rest ih => exact ih _ (intern_nodup _ _ h)
  unfold importVista
  rw [← Array.foldl_toList]
  exact fold source.nodes.toList (pool, #[]) distinct

end Counting.Executable
