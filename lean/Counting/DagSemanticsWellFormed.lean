import Counting.DagSemanticsImport

namespace Counting.Executable

theorem bundleKeys_addCount (property : Nat → Prop) (index count : Nat)
    (bundles : List (Nat × Nat)) (newKey : property index)
    (oldKeys : ∀ edge ∈ bundles, property edge.1) :
    ∀ edge ∈ addCount index count bundles, property edge.1 := by
  induction bundles with
  | nil =>
      by_cases h : count = 0 <;> simp [addCount, h, newKey]
  | cons pair rest ih =>
      rcases pair with ⟨i, c⟩
      have head : property i := oldKeys (i, c) (by simp)
      have tail : ∀ edge ∈ rest, property edge.1 := fun edge h => oldKeys edge (by simp [h])
      have recur := ih tail
      by_cases hc : count = 0
      · simpa only [addCount, beq_iff_eq, hc, if_true] using oldKeys
      by_cases hi : index = i
      · subst i
        simp only [addCount, beq_iff_eq, hc, if_false, if_true, List.mem_cons, forall_eq_or_imp]
        exact ⟨head, tail⟩
      by_cases hlt : index < i
      · simp only [addCount, beq_iff_eq, hc, hi, hlt, if_false, if_true,
          List.mem_cons, forall_eq_or_imp]
        exact ⟨newKey, head, tail⟩
      · simp only [addCount, beq_iff_eq, hc, hi, hlt, if_false,
          List.mem_cons, forall_eq_or_imp]
        exact ⟨head, recur⟩

theorem bundleKeys_reindex (property : Nat → Prop) (mapping : Array Nat)
    (bundles accumulated : List (Nat × Nat))
    (mapped : ∀ edge ∈ bundles, property (mapping[edge.1]?.getD 0))
    (old : ∀ edge ∈ accumulated, property edge.1) :
    ∀ edge ∈ bundles.foldl
      (fun acc edge => addCount (mapping[edge.1]?.getD 0) edge.2 acc) accumulated,
      property edge.1 := by
  induction bundles generalizing accumulated with
  | nil => exact old
  | cons edge rest ih =>
      apply ih
      · intro e he
        exact mapped e (by simp [he])
      · exact bundleKeys_addCount property _ _ _ (mapped edge (by simp)) old

theorem referenceMap_keys (property : Nat → Prop) (mapping : Array Nat) (node : Node)
    (mapped : ∀ edge ∈ node.incoming, property (mapping[edge.1]?.getD 0)) :
    ∀ edge ∈ (referenceMap mapping node).incoming, property edge.1 :=
  bundleKeys_reindex property mapping node.incoming [] mapped (by simp)

/-- A node may be appended once its strict lower-level references are stored. -/
def Ready (vista : Vista) (node : Node) : Prop :=
  node.level = 0 ∨
    ∃ parent, node.parent = some parent ∧ parent < vista.nodes.size ∧
      (vista.node parent).level + 1 = node.level ∧
      ∀ edge ∈ node.incoming,
        edge.1 < vista.nodes.size ∧ (vista.node edge.1).level + 1 = node.level

theorem wellFormed_push (vista : Vista) (node : Node)
    (wellFormed : WellFormed vista) (ready : Ready vista node) :
    WellFormed ⟨vista.nodes.push node, vista.bottom⟩ := by
  intro i hi
  have hib : i ≤ vista.nodes.size := Nat.le_of_lt_succ (by simpa only [Array.size_push] using hi)
  rcases lt_or_eq_of_le hib with hlt | rfl
  · rw [node_push_old _ _ _ _ hlt]
    rcases wellFormed i hlt with hz | ⟨p, hp, hpi, hpl, incoming⟩
    · exact Or.inl hz
    · right
      refine ⟨p, hp, hpi, ?_, ?_⟩
      · simpa only [node_push_old _ _ _ _ (hpi.trans hlt)] using hpl
      · intro edge he
        obtain ⟨hei, hel⟩ := incoming edge he
        exact ⟨hei, by simpa only [node_push_old _ _ _ _ (hei.trans hlt)] using hel⟩
  · rw [node_push_last]
    rcases ready with hz | ⟨p, hp, hpi, hpl, incoming⟩
    · exact Or.inl hz
    · right
      refine ⟨p, hp, hpi, ?_, ?_⟩
      · simpa only [node_push_old _ _ _ _ hpi] using hpl
      · intro edge he
        obtain ⟨hei, hel⟩ := incoming edge he
        exact ⟨hei, by simpa only [node_push_old _ _ _ _ hei] using hel⟩

theorem intern_wellFormed (nodes : Array Node) (node : Node)
    (wellFormed : WellFormed ⟨nodes, 0⟩) (ready : Ready ⟨nodes, 0⟩ node) :
    WellFormed ⟨(intern nodes node).1, 0⟩ := by
  unfold intern
  split
  · exact wellFormed
  · exact wellFormed_push ⟨nodes, 0⟩ node wellFormed ready

theorem referenceMap_ready (source target : Vista) (mapping : Array Nat) (node : Node)
    (ready : Ready source node) (relabels : Relabels source target mapping)
    (bounded : ∀ i, i < source.nodes.size → mapping[i]?.getD 0 < target.nodes.size) :
    Ready target (referenceMap mapping node) := by
  rcases ready with hz | ⟨p, hp, hpi, hpl, incoming⟩
  · exact Or.inl hz
  · right
    have levelEqual (i : Nat) (hi : i < source.nodes.size) :
        (target.node (mapping[i]?.getD 0)).level = (source.node i).level :=
      by simpa only [referenceMap] using congrArg Node.level (relabels i hi)
    refine ⟨mapping[p]?.getD 0, ?_, bounded p hpi, ?_, ?_⟩
    · simp only [referenceMap, hp, Option.map_some]
    · simpa only [referenceMap, levelEqual p hpi] using hpl
    · change ∀ edge ∈ (referenceMap mapping node).incoming,
        edge.1 < target.nodes.size ∧ (target.node edge.1).level + 1 = node.level
      apply referenceMap_keys (fun i => i < target.nodes.size ∧
        (target.node i).level + 1 = node.level) mapping node
      intro edge he
      obtain ⟨hei, hel⟩ := incoming edge he
      exact ⟨bounded _ hei, by simpa only [levelEqual _ hei] using hel⟩

theorem wellFormed_of_push (nodes : Array Node) (node : Node) (bottom : Nat)
    (wellFormed : WellFormed ⟨nodes.push node, bottom⟩) :
    WellFormed ⟨nodes, bottom⟩ ∧ Ready ⟨nodes, bottom⟩ node := by
  constructor
  · intro i hi
    have entry := wellFormed i (by simpa only [Array.size_push] using Nat.lt_succ_of_lt hi)
    rw [node_push_old _ _ _ _ hi] at entry
    rcases entry with hz | ⟨p, hp, hpi, hpl, incoming⟩
    · exact Or.inl hz
    · right
      refine ⟨p, hp, hpi, ?_, ?_⟩
      · simpa only [node_push_old _ _ _ _ (hpi.trans hi)] using hpl
      · intro edge he
        obtain ⟨hei, hel⟩ := incoming edge he
        exact ⟨hei, by simpa only [node_push_old _ _ _ _ (hei.trans hi)] using hel⟩
  · have entry := wellFormed nodes.size (by simp)
    rw [node_push_last] at entry
    rcases entry with hz | ⟨p, hp, hpi, hpl, incoming⟩
    · exact Or.inl hz
    · right
      refine ⟨p, hp, hpi, ?_, ?_⟩
      · simpa only [node_push_old _ _ _ _ hpi] using hpl
      · intro edge he
        obtain ⟨hei, hel⟩ := incoming edge he
        exact ⟨hei, by simpa only [node_push_old _ _ _ _ hei] using hel⟩

theorem importVista_wellFormed (pool : Array Node) (source : Vista)
    (poolWellFormed : WellFormed ⟨pool, 0⟩) (sourceWellFormed : WellFormed source)
    (topological : Topological source) :
    WellFormed ⟨(importVista pool source).1, 0⟩ := by
  rcases source with ⟨⟨nodes⟩, bottom⟩
  induction nodes using List.reverseRecOn with
  | nil => exact poolWellFormed
  | append_singleton nodes node ih =>
      let previous : Vista := ⟨⟨nodes⟩, bottom⟩
      have pushed : (⟨nodes ++ [node]⟩ : Array Node) = previous.nodes.push node := by
        apply Array.ext'
        simp [previous]
      rw [pushed] at sourceWellFormed topological ⊢
      have oldTopo : Topological previous := by
        intro i hi
        have h := topological i (by simpa only [Array.size_push] using Nat.lt_succ_of_lt hi)
        simpa only [node_push_old _ _ _ _ hi] using h
      obtain ⟨oldWellFormed, ready⟩ := wellFormed_of_push _ _ _ sourceWellFormed
      have beforeWellFormed := ih oldWellFormed oldTopo
      have beforeCorrect := importVista_correct pool previous oldTopo
      rw [importVista_push]
      exact intern_wellFormed _ _ beforeWellFormed
        (referenceMap_ready previous _ _ node ready beforeCorrect.2.2.2 beforeCorrect.2.2.1)

/-- Existing histories are unchanged when another valid vista is imported. -/
theorem importVista_preserves_pool (pool : Vista) (source : Vista)
    (poolWellFormed : WellFormed pool) (topological : Topological source)
    (index : Nat) (inside : index < pool.nodes.size) :
    decodeNode ⟨(importVista pool.nodes source).1, 0⟩ (pool.node index).level index =
      decodeNode pool (pool.node index).level index :=
  decodeNode_eq_of_extends pool _ poolWellFormed
    (importVista_correct pool.nodes source topological).2.1 index inside

end Counting.Executable
