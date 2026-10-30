import Counting.DagSemanticsValidityCanonical

namespace Counting.Executable

/-- Interning creates no pool nodes other than the supplied signature. -/
theorem intern_index_covered (nodes : Array Node) (node : Node)
    (j : Nat) (inside : j < (intern nodes node).1.size) :
    j < nodes.size ∨ j = (intern nodes node).2 := by
  unfold intern at inside ⊢
  split at inside <;> rename_i found
  · exact Or.inl inside
  · simp only [Array.size_push] at inside
    omega

/-- Every imported pool node comes from the old pool or an actual source node. -/
theorem importVista_covered (pool : Array Node) (source : Vista)
    (j : Nat) (inside : j < (importVista pool source).1.size) :
    j < pool.size ∨ ∃ i, i < source.nodes.size ∧
      (importVista pool source).2[i]?.getD 0 = j := by
  rcases source with ⟨⟨nodes⟩, bottom⟩
  induction nodes using List.reverseRecOn generalizing j with
  | nil => exact Or.inl inside
  | append_singleton nodes node ih =>
      let previous : Vista := ⟨⟨nodes⟩, bottom⟩
      have pushed : (⟨nodes ++ [node]⟩ : Array Node) = previous.nodes.push node := by
        apply Array.ext'
        simp [previous]
      rw [pushed, importVista_push] at inside ⊢
      let before := importVista pool previous
      let next := intern before.1 (referenceMap before.2 node)
      have mapSize : before.2.size = previous.nodes.size := importVista_mapping_size pool previous
      change j < next.1.size at inside
      change j < pool.size ∨ ∃ i, i < (previous.nodes.push node).size ∧
        (before.2.push next.2)[i]?.getD 0 = j
      rcases intern_index_covered before.1 (referenceMap before.2 node) j inside with old | equal
      · rcases ih j old with poolOld | ⟨i, hi, heq⟩
        · exact Or.inl poolOld
        · change i < previous.nodes.size at hi
          change before.2[i]?.getD 0 = j at heq
          refine Or.inr ⟨i, by simp only [Array.size_push]; omega, ?_⟩
          have mapInside : i < before.2.size := by rw [mapSize]; exact hi
          simpa only [Array.getElem?_push_lt mapInside, Array.getElem?_eq_getElem mapInside] using heq
      · refine Or.inr ⟨previous.nodes.size, by simp, ?_⟩
        rw [← mapSize, Array.getElem?_push_size, Option.getD_some]
        exact equal.symm

theorem addCount_old_mem (key count : Nat) (bundles : List (Nat × Nat))
    (edge : Nat × Nat) (member : edge ∈ bundles) (positive : 0 < edge.2) :
    ∃ result ∈ addCount key count bundles, result.1 = edge.1 := by
  have appears : edge.1 ∈ bundleMessages id (addCount key count bundles) := by
    rw [bundleMessages_addCount]
    exact Multiset.mem_add.mpr (Or.inr ((mem_bundleMessages _ _ _).mpr ⟨edge, member, positive, rfl⟩))
  obtain ⟨result, hr, _, equal⟩ := (mem_bundleMessages _ _ _).mp appears
  exact ⟨result, hr, equal⟩

theorem addCount_new_mem (key count : Nat) (bundles : List (Nat × Nat)) (positive : 0 < count) :
    ∃ result ∈ addCount key count bundles, result.1 = key := by
  have appears : key ∈ bundleMessages id (addCount key count bundles) := by
    rw [bundleMessages_addCount]
    exact Multiset.mem_add.mpr (Or.inl (Multiset.mem_replicate.mpr ⟨Nat.ne_of_gt positive, rfl⟩))
  obtain ⟨result, hr, _, equal⟩ := (mem_bundleMessages _ _ _).mp appears
  exact ⟨result, hr, equal⟩

def MergeReachable (ownBottom : Nat) (state : MergeState) : Prop :=
  ∀ j, j < state.1.size → DagReach ⟨state.1, 0⟩ ownBottom j ∨
    ∃ edge ∈ state.2, DagReach ⟨state.1, 0⟩ edge.1 j

theorem mergeMessage_reachable (ownBottom : Nat) (state : MergeState) (message : Vista × Nat)
    (reachable : MergeReachable ownBottom state) (sparse : Sparse state.2)
    (valid : message.1.valid = true) (positive : 0 < message.2) :
    MergeReachable ownBottom (mergeMessage state message) := by
  let imported := importVista state.1 message.1
  let index := imported.2[message.1.bottom]?.getD 0
  have correct := importVista_correct state.1 message.1 (topological_of_valid _ valid)
  have bottomEdge : ∃ edge ∈ addCount index message.2 state.2, edge.1 = index :=
    addCount_new_mem _ _ _ positive
  intro j hj
  change j < imported.1.size at hj
  change DagReach ⟨imported.1, 0⟩ ownBottom j ∨
    ∃ edge ∈ addCount index message.2 state.2, DagReach ⟨imported.1, 0⟩ edge.1 j
  rcases importVista_covered state.1 message.1 j hj with old | ⟨i, hi, equal⟩
  · rcases reachable j old with own | ⟨edge, he, reach⟩
    · exact Or.inl (own.extends correct.2.1 correct.1)
    · obtain ⟨result, hr, key⟩ := addCount_old_mem index message.2 state.2 edge he (sparse.2 edge he)
      exact Or.inr ⟨result, hr, key ▸ reach.extends correct.2.1 correct.1⟩
  · have reach := (allReachable_of_valid message.1 valid i hi).relabels imported.2
      (nodesValid_of_valid message.1 valid) correct.2.2.2 correct.2.2.1
    rw [equal] at reach
    obtain ⟨edge, he, key⟩ := bottomEdge
    exact Or.inr ⟨edge, he, key ▸ reach⟩

theorem mergeMessages_valid_reachable (ownBottom : Nat) (state : MergeState)
    (received : List (Vista × Nat))
    (validNodes : NodesValid ⟨state.1, 0⟩) (sparse : Sparse state.2)
    (reachable : MergeReachable ownBottom state)
    (valid : ∀ message ∈ received, message.1.valid = true ∧ 0 < message.2) :
    NodesValid ⟨(received.foldl mergeMessage state).1, 0⟩ ∧
    Sparse (received.foldl mergeMessage state).2 ∧
    MergeReachable ownBottom (received.foldl mergeMessage state) := by
  induction received generalizing state with
  | nil => exact ⟨validNodes, sparse, reachable⟩
  | cons message rest ih =>
      obtain ⟨messageValid, positive⟩ := valid message (by simp)
      exact ih (mergeMessage state message)
        (importVista_nodesValid state.1 message.1 validNodes (nodesValid_of_valid _ messageValid))
        (sparse_addCount _ _ _ sparse)
        (mergeMessage_reachable ownBottom state message reachable sparse messageValid positive)
        (fun m hm => valid m (by simp [hm]))

end Counting.Executable
