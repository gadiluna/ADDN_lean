import Counting.DagSemanticsValidity

namespace Counting.Executable

/-- Every stored node in a valid vista is at or below its bottom level. -/
theorem valid_node_level_le_bottom (vista : Vista) (valid : vista.valid = true) :
    AllNodes (fun node => node.level ≤ (vista.node vista.bottom).level) vista.nodes := by
  apply (allNodes_iff (fun node => node.level ≤ (vista.node vista.bottom).level) vista).mpr
  apply valid_nodes_induction vista valid (fun i => (vista.node i).level ≤ (vista.node vista.bottom).level)
  · exact le_rfl
  · intro i hi bound p parent
    rcases nodeReady_of_check vista i hi (nodesValid_of_valid vista valid i hi) with
      ⟨_, absent, _, _⟩ | ⟨_, q, eq, _, level, _⟩
    · rw [absent] at parent
      contradiction
    · have same : q = p := Option.some.inj (eq.symm.trans parent)
      subst q
      omega
  · intro i hi bound edge present
    rcases nodeReady_of_check vista i hi (nodesValid_of_valid vista valid i hi) with
      ⟨_, _, _, absent⟩ | ⟨_, _, _, _, _, _, _, incoming⟩
    · rw [absent] at present
      contradiction
    · have level := (incoming edge present).2
      omega

theorem mergeMessages_nodup (state : MergeState) (received : List (Vista × Nat))
    (distinct : state.1.toList.Nodup) :
    (received.foldl mergeMessage state).1.toList.Nodup := by
  induction received generalizing state with
  | nil => exact distinct
  | cons message rest ih =>
      exact ih (mergeMessage state message) (importVista_nodup state.1 message.1 distinct)

theorem mergeMessages_levels (depth : Nat) (state : MergeState) (received : List (Vista × Nat))
    (bounded : AllNodes (fun node => node.level ≤ depth) state.1)
    (messages : ∀ message ∈ received,
      AllNodes (fun node => node.level ≤ depth) message.1.nodes) :
    AllNodes (fun node => node.level ≤ depth) (received.foldl mergeMessage state).1 := by
  induction received generalizing state with
  | nil => exact bounded
  | cons message rest ih =>
      exact ih (mergeMessage state message)
        (importVista_allNodes (fun node => node.level ≤ depth) (fun _ _ h => h)
          state.1 message.1 bounded (messages message (by simp)))
        (fun m hm => messages m (by simp [hm]))

/-- Canonical ordering is unnecessary for validity: imports already merge
equal signatures, and the appended node has a strictly new level. -/
theorem rawUpdate_nodup (old : Vista) (received : List (Vista × Nat)) (outdegree : Nat)
    (valid : old.valid = true)
    (receivedValid : ∀ message ∈ received, message.1.valid = true ∧
      (message.1.node message.1.bottom).level = (old.node old.bottom).level) :
    (rawUpdate old received outdegree).nodes.toList.Nodup := by
  let depth := (old.node old.bottom).level
  let start := importVista #[] old
  let merged := received.foldl mergeMessage (start.1, [])
  let node : Node := ⟨depth+1, some (start.2[old.bottom]?.getD 0),
    (old.node old.bottom).leader, outdegree, merged.2⟩
  have distinct : merged.1.toList.Nodup :=
    mergeMessages_nodup (start.1, []) received (importVista_nodup #[] old (by simp))
  have initial : AllNodes (fun node => node.level ≤ depth) start.1 :=
    importVista_allNodes (fun node => node.level ≤ depth) (fun _ _ h => h) #[] old
      (by intro n hn; simp at hn) (valid_node_level_le_bottom old valid)
  have bounded : AllNodes (fun node => node.level ≤ depth) merged.1 :=
    mergeMessages_levels depth (start.1, []) received initial (by
      intro message member
      obtain ⟨messageValid, level⟩ := receivedValid message member
      simpa only [level] using valid_node_level_le_bottom message.1 messageValid)
  change (merged.1.push node).toList.Nodup
  rw [Array.toList_push, List.nodup_append]
  refine ⟨distinct, by simp, ?_⟩
  intro x hx y hy
  simp only [List.mem_singleton] at hy
  subst y
  intro same
  subst x
  have impossible := bounded node hx
  change depth+1 ≤ depth at impossible
  omega

/-- The unnormalized local update itself satisfies the complete executable
vista validator. It can be used by offline network reconstruction. -/
theorem rawUpdate_valid (old : Vista) (received : List (Vista × Nat)) (outdegree : Nat)
    (valid : old.valid = true)
    (receivedValid : ∀ message ∈ received, message.1.valid = true ∧ 0 < message.2 ∧
      (message.1.node message.1.bottom).level = (old.node old.bottom).level) :
    (rawUpdate old received outdegree).valid = true := by
  obtain ⟨nodes, reachable⟩ := rawUpdate_valid_properties old received outdegree valid receivedValid
  exact valid_of_properties _ (rawUpdate_bottom_lt old received outdegree) nodes
    (rawUpdate_nodup old received outdegree valid
      (fun m hm => ⟨(receivedValid m hm).1, (receivedValid m hm).2.2⟩)) reachable

end Counting.Executable
