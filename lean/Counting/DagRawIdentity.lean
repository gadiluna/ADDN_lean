import Counting.DagRawValidity

namespace Counting.Executable

/-- Sparse sorted labels are fixed by identity reference rewriting. -/
theorem referenceMap_identity (mapping : Array Nat) (node : Node)
    (parentIdentity : ∀ p, node.parent = some p → mapping[p]?.getD 0 = p)
    (incomingIdentity : ∀ edge ∈ node.incoming, mapping[edge.1]?.getD 0 = edge.1)
    (sorted : countsSorted node.incoming = true) : referenceMap mapping node = node := by
  refine node_eq_of_fields (referenceMap mapping node) node rfl ?_ rfl rfl ?_
  · change node.parent.map (fun i => mapping[i]?.getD 0) = node.parent
    cases h : node.parent with
    | none => rfl
    | some p => simp only [Option.map_some, parentIdentity p h]
  · apply bundleMessages_eq_implies_bundles_eq (fun i : Nat => i)
      _ _ (sparse_of_countsSorted _ (referenceMap_countsSorted mapping node))
      (sparse_of_countsSorted _ sorted) (by intros; assumption)
    rw [bundleMessages_referenceMap]
    exact bundleMessages_congr _ _ _ incomingIdentity

theorem referenceMap_range (nodes : Array Node) (node : Node) (bottom : Nat)
    (ready : NodeReady ⟨nodes, bottom⟩ node) :
    referenceMap (List.range nodes.size).toArray node = node := by
  apply referenceMap_identity
  · intro p hp
    rcases ready with ⟨_, absent, _, _⟩ | ⟨_, q, same, inside, _⟩
    · rw [absent] at hp
      contradiction
    · have equal : p = q := Option.some.inj (hp.symm.trans same)
      subst q
      simp [inside]
  · intro edge member
    rcases ready with ⟨_, _, _, absent⟩ | ⟨_, _, _, _, _, _, _, incoming⟩
    · rw [absent] at member
      contradiction
    · simp [(incoming edge member).1]
  · rcases ready with ⟨_, _, _, absent⟩ | ⟨_, _, _, _, _, _, sorted, _⟩
    · simp [absent, countsSorted]
    · exact sorted

theorem intern_fresh (nodes : Array Node) (node : Node) (absent : node ∉ nodes.toList) :
    intern nodes node = (nodes.push node, nodes.size) := by
  have empty : (List.range nodes.size).find? (fun i => nodes[i]?.getD default == node) = none := by
    apply List.find?_eq_none.mpr
    intro i member
    have inside := List.mem_range.mp member
    have neq : nodes[i] ≠ node := by
      intro same
      exact absent (same ▸ (Array.mem_toList_iff.mpr (Array.getElem_mem inside)))
    simp [Array.getElem?_eq_getElem inside, neq]
  simp only [intern, empty]

/-- Reimporting a valid topological, signature-distinct array into the
empty pool is exactly the identity, including its reference table. -/
theorem importVista_empty_identity_of_nodes (source : Vista)
    (valid : NodesValid source) (distinct : source.nodes.toList.Nodup) :
    importVista #[] source = (source.nodes, (List.range source.nodes.size).toArray) := by
  rcases source with ⟨⟨nodes⟩, bottom⟩
  induction nodes using List.reverseRecOn with
  | nil => rfl
  | append_singleton nodes node ih =>
      let previous : Vista := ⟨⟨nodes⟩, bottom⟩
      have pushed : (⟨nodes ++ [node]⟩ : Array Node) = previous.nodes.push node := by
        apply Array.ext'
        simp [previous]
      rw [pushed] at valid distinct ⊢
      obtain ⟨oldValid, ready⟩ := nodesValid_of_push _ _ _ valid
      have oldDistinct : previous.nodes.toList.Nodup := by
        rw [Array.toList_push, List.nodup_append] at distinct
        exact distinct.1
      have absent : node ∉ previous.nodes.toList := by
        rw [Array.toList_push, List.nodup_append] at distinct
        intro member
        exact distinct.2.2 node member node (by simp) rfl
      rw [importVista_push, ih oldValid oldDistinct]
      change ((intern previous.nodes (referenceMap (List.range previous.nodes.size).toArray node)).1,
        (List.range previous.nodes.size).toArray.push
          (intern previous.nodes (referenceMap (List.range previous.nodes.size).toArray node)).2) = _
      rw [referenceMap_range previous.nodes node bottom ready, intern_fresh _ _ absent]
      congr 1
      apply Array.ext'
      simp [List.range_succ]

theorem importVista_empty_identity (source : Vista) (valid : source.valid = true) :
    importVista #[] source = (source.nodes, (List.range source.nodes.size).toArray) :=
  importVista_empty_identity_of_nodes source (nodesValid_of_valid source valid)
    (nodes_nodup_of_valid source valid)

/-- The physical offline update may start with the existing pool and its
bottom index; no preliminary import or identity-table construction is needed. -/
theorem rawUpdate_starting_old (old : Vista) (received : List (Vista × Nat)) (outdegree : Nat)
    (valid : old.valid = true) :
    rawUpdate old received outdegree =
      let merged := received.foldl mergeMessage (old.nodes, [])
      ⟨merged.1.push ⟨(old.node old.bottom).level+1, some old.bottom,
        (old.node old.bottom).leader, outdegree, merged.2⟩, merged.1.size⟩ := by
  have inside : old.bottom < old.nodes.size := by
    simp only [Vista.valid, Bool.and_eq_true, decide_eq_true_eq] at valid
    exact valid.1.1.1
  simp [rawUpdate, importVista_empty_identity old valid, inside]

/-- The receiver's new signature is fresh in the merged old-round pool,
so the physical intern primitive performs exactly the required append. -/
theorem rawUpdate_starting_old_intern (old : Vista) (received : List (Vista × Nat)) (outdegree : Nat)
    (valid : old.valid = true)
    (receivedValid : ∀ message ∈ received, message.1.valid = true ∧
      (message.1.node message.1.bottom).level = (old.node old.bottom).level) :
    let merged := received.foldl mergeMessage (old.nodes, [])
    let node : Node := ⟨(old.node old.bottom).level+1, some old.bottom,
      (old.node old.bottom).leader, outdegree, merged.2⟩
    intern merged.1 node = (merged.1.push node, merged.1.size) := by
  let merged := received.foldl mergeMessage (old.nodes, [])
  let node : Node := ⟨(old.node old.bottom).level+1, some old.bottom,
    (old.node old.bottom).leader, outdegree, merged.2⟩
  have distinct := rawUpdate_nodup old received outdegree valid receivedValid
  rw [rawUpdate_starting_old old received outdegree valid] at distinct
  change (merged.1.push node).toList.Nodup at distinct
  apply intern_fresh
  intro member
  rw [Array.toList_push, List.nodup_append] at distinct
  exact distinct.2.2 node member node (by simp) rfl

end Counting.Executable
