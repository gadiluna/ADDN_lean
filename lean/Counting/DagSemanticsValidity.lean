import Counting.DagSemanticsValidityImport

namespace Counting.Executable

/-- The unnormalized update already has correct nodes and no unreachable garbage.
Uniqueness of stored signatures is supplied by the actual canonicalization pass. -/
theorem rawUpdate_valid_properties (old : Vista) (received : List (Vista × Nat)) (outdegree : Nat)
    (valid : old.valid = true)
    (receivedValid : ∀ message ∈ received, message.1.valid = true ∧ 0 < message.2 ∧
      (message.1.node message.1.bottom).level = (old.node old.bottom).level) :
    NodesValid (rawUpdate old received outdegree) ∧ AllReachable (rawUpdate old received outdegree) := by
  let depth := (old.node old.bottom).level
  let start := importVista #[] old
  let ownBottom := start.2[old.bottom]?.getD 0
  let merged := received.foldl mergeMessage (start.1, [])
  let node : Node := ⟨depth+1, some ownBottom, (old.node old.bottom).leader, outdegree, merged.2⟩
  let result : Vista := ⟨merged.1.push node, merged.1.size⟩
  have inside : old.bottom < old.nodes.size := by
    simp only [Vista.valid, Bool.and_eq_true, decide_eq_true_eq] at valid
    exact valid.1.1.1
  have imported := importVista_correct #[] old (topological_of_valid _ valid)
  have startNodes : NodesValid ⟨start.1, 0⟩ :=
    importVista_nodesValid #[] old (by intro i hi; simp at hi) (nodesValid_of_valid _ valid)
  have startReach : MergeReachable ownBottom (start.1, []) := by
    intro j hj
    rcases importVista_covered #[] old j hj with impossible | ⟨i, hi, equal⟩
    · simp at impossible
    · left
      change start.2[i]?.getD 0 = j at equal
      have reach := (allReachable_of_valid old valid i hi).relabels start.2
        (nodesValid_of_valid _ valid) imported.2.2.2 imported.2.2.1
      simpa only [equal] using reach
  have mergedSafe := mergeMessages_valid_reachable ownBottom (start.1, []) received
    startNodes (by simp [Sparse]) startReach
    (fun m hm => ⟨(receivedValid m hm).1, (receivedValid m hm).2.1⟩)
  have startInvariant : PoolInvariant depth (start.1, []) :=
    ⟨importVista_wellFormed #[] old (by intro i hi; simp at hi)
        (wellFormed_of_valid _ valid) (topological_of_valid _ valid),
      importVista_baseClean #[] old (by intro n hn; simp at hn) (baseClean_of_valid _ valid),
      by intro edge he; contradiction⟩
  have mergedCorrect := mergeMessages_correct depth received (start.1, []) startInvariant
    (fun m hm => ⟨(receivedValid m hm).1, (receivedValid m hm).2.2⟩)
  have ownInside : ownBottom < start.1.size := imported.2.2.1 old.bottom inside
  have ownMerged : ownBottom < merged.1.size := ownInside.trans_le mergedCorrect.size
  have ownFields : ((Vista.mk merged.1 0).node ownBottom).level = depth ∧
      ((Vista.mk merged.1 0).node ownBottom).leader = (old.node old.bottom).leader := by
    rw [mergedCorrect.extension ownBottom ownInside, imported.2.2.2 old.bottom inside]
    exact ⟨rfl, rfl⟩
  have ready : NodeReady ⟨merged.1, 0⟩ node := by
    right
    refine ⟨by simp [node], ownBottom, rfl, ownMerged,
      congrArg (·+1) ownFields.1, ownFields.2, countsSorted_of_sparse _ mergedSafe.2.1, ?_⟩
    intro edge he
    obtain ⟨hei, hel⟩ := mergedCorrect.invariant.incomingAt edge he
    exact ⟨hei, congrArg (·+1) hel⟩
  have validResult : NodesValid result :=
    nodesValid_push ⟨merged.1, merged.1.size⟩ node mergedSafe.1 ready
  have extension : Extends ⟨merged.1, 0⟩ result := fun i hi => node_push_old _ _ _ _ hi
  have size : merged.1.size ≤ result.nodes.size := by simp [result]
  have bottomInside : result.bottom < result.nodes.size := by simp [result]
  have ownReach : DagReach result result.bottom ownBottom := by
    apply DagReach.parent .root bottomInside
    rw [node_push_last]
  have reachableResult : AllReachable result := by
    intro j hj
    have le : j ≤ merged.1.size := Nat.le_of_lt_succ (by simpa only [result, Array.size_push] using hj)
    rcases lt_or_eq_of_le le with old | rfl
    · rcases mergedSafe.2.2 j old with own | ⟨edge, he, reach⟩
      · exact ownReach.trans (own.extends extension size)
      · have edgeReach : DagReach result result.bottom edge.1 := by
          apply DagReach.incoming .root bottomInside
          rw [node_push_last]
          exact he
        exact edgeReach.trans (reach.extends extension size)
    · exact .root
  exact ⟨validResult, reachableResult⟩

/-- A successful call to the existing updater always passes its exact validator. -/
theorem updateVista_valid (old : Vista) (received : List (Vista × Nat)) (outdegree : Nat)
    (next : Vista) (success : updateVista? old received outdegree = some next) : next.valid = true := by
  have valid : old.valid = true := by
    cases hv : old.valid with
    | false => simp [updateVista?, hv] at success
    | true => rfl
  have check : received.all (fun message => message.2 > 0 && message.1.valid &&
      (message.1.node message.1.bottom).level == (old.node old.bottom).level) = true := by
    cases hr : received.all (fun message => message.2 > 0 && message.1.valid &&
        (message.1.node message.1.bottom).level == (old.node old.bottom).level) with
    | false => simp [updateVista?, valid, hr] at success
    | true => rfl
  have receivedValid : ∀ message ∈ received, message.1.valid = true ∧ 0 < message.2 ∧
      (message.1.node message.1.bottom).level = (old.node old.bottom).level := by
    intro message hm
    have h := List.all_eq_true.mp check message hm
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    exact ⟨h.1.2, h.1.1, h.2⟩
  have identify : next = canonicalize (rawUpdate old received outdegree) := by
    rw [updateVista_defined old received outdegree valid check] at success
    exact Option.some.inj success.symm
  rw [identify]
  have properties := rawUpdate_valid_properties old received outdegree valid receivedValid
  exact canonicalize_valid_of_properties _ (rawUpdate_bottom_lt old received outdegree)
    properties.1 properties.2

/-- Valid inputs of a common round always produce a valid next vista. -/
theorem updateVista_total (old : Vista) (received : List (Vista × Nat)) (outdegree : Nat)
    (valid : old.valid = true)
    (receivedValid : ∀ message ∈ received, message.1.valid = true ∧ 0 < message.2 ∧
      (message.1.node message.1.bottom).level = (old.node old.bottom).level) :
    ∃ next, updateVista? old received outdegree = some next ∧ next.valid = true ∧
      (next.node next.bottom).level = (old.node old.bottom).level + 1 := by
  have check : received.all (fun message => message.2 > 0 && message.1.valid &&
      (message.1.node message.1.bottom).level == (old.node old.bottom).level) = true := by
    apply List.all_eq_true.mpr
    intro message hm
    obtain ⟨messageValid, positive, level⟩ := receivedValid message hm
    simp only [messageValid, level, beq_self_eq_true, Bool.and_true,
      decide_eq_true_eq, positive]
  have success := updateVista_defined old received outdegree valid check
  exact ⟨_, success, updateVista_valid _ _ _ _ success, (updateVista_sound _ _ _ _ success).1⟩

@[simp] theorem initialVista_valid (leader : Bool) : (initialVista leader).valid = true := by
  apply valid_of_properties
  · simp [initialVista]
  · intro i hi
    have eq : i = 0 := by change i < 1 at hi; omega
    subst i
    simp [initialVista, nodeValid, Vista.node]
  · simp [initialVista]
  · intro i hi
    have eq : i = 0 := by change i < 1 at hi; omega
    subst i
    exact .root

end Counting.Executable
