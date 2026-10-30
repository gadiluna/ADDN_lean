import Counting.DagSemanticsStructure

namespace Counting.Executable

theorem decodeNode_bottom_irrel (nodes : Array Node) (left right depth : Nat) :
    decodeNode ⟨nodes, left⟩ depth = decodeNode ⟨nodes, right⟩ depth := by
  induction depth with
  | zero => rfl
  | succ depth ih =>
      funext i
      simp only [decodeNode, ih]
      rfl

abbrev MergeState := Array Node × List (Nat × Nat)

def mergeMessage (state : MergeState) (message : Vista × Nat) : MergeState :=
  let (next, mapping) := importVista state.1 message.1
  (next, addCount (mapping[message.1.bottom]?.getD 0) message.2 state.2)

theorem mergeMessage_eq : mergeMessage = fun state message =>
    ((importVista state.1 message.1).1,
      addCount ((importVista state.1 message.1).2[message.1.bottom]?.getD 0) message.2 state.2) := rfl

def rawUpdate (old : Vista) (received : List (Vista × Nat)) (outdegree : Nat) : Vista :=
  let start := importVista #[] old
  let ownBottom := start.2[old.bottom]?.getD 0
  let merged := received.foldl mergeMessage (start.1, [])
  let node : Node := ⟨(old.node old.bottom).level + 1, some ownBottom,
    (old.node old.bottom).leader, outdegree, merged.2⟩
  ⟨merged.1.push node, merged.1.size⟩

def IncomingAt (depth : Nat) (state : MergeState) : Prop :=
  ∀ edge ∈ state.2, edge.1 < state.1.size ∧ ((Vista.mk state.1 0).node edge.1).level = depth

structure PoolInvariant (depth : Nat) (state : MergeState) : Prop where
  wellFormed : WellFormed ⟨state.1, 0⟩
  baseClean : BaseClean ⟨state.1, 0⟩
  incomingAt : IncomingAt depth state

def receivedHistories (depth : Nat) (received : List (Vista × Nat)) : Multiset (Counting.FullHistory depth) :=
  (received.map (fun message =>
    Multiset.replicate message.2 (decodeNode message.1 depth message.1.bottom))).sum

theorem Extends.trans {a b c : Vista} (ab : Extends a b) (bc : Extends b c)
    (size : a.nodes.size ≤ b.nodes.size) : Extends a c := by
  intro i hi
  exact (bc i (hi.trans_le size)).trans (ab i hi)

theorem bundleMessages_eq_of_extends (depth : Nat) (before after : MergeState)
    (invariant : PoolInvariant depth before)
    (extension : Extends ⟨before.1, 0⟩ ⟨after.1, 0⟩) :
    bundleMessages (decodeNode ⟨after.1, 0⟩ depth) before.2 =
      bundleMessages (decodeNode ⟨before.1, 0⟩ depth) before.2 := by
  apply bundleMessages_congr
  intro edge he
  obtain ⟨inside, level⟩ := invariant.incomingAt edge he
  have h := decodeNode_eq_of_extends ⟨before.1, 0⟩ ⟨after.1, 0⟩
    invariant.wellFormed extension edge.1 inside
  rw [level] at h
  exact h

structure MergeCorrect (depth : Nat) (before after : MergeState)
    (messages : Multiset (Counting.FullHistory depth)) : Prop where
  invariant : PoolInvariant depth after
  size : before.1.size ≤ after.1.size
  extension : Extends ⟨before.1, 0⟩ ⟨after.1, 0⟩
  messages : bundleMessages (decodeNode ⟨after.1, 0⟩ depth) after.2 =
    bundleMessages (decodeNode ⟨before.1, 0⟩ depth) before.2 + messages

theorem mergeMessage_correct (depth : Nat) (before : MergeState)
    (invariant : PoolInvariant depth before) (message : Vista × Nat)
    (valid : message.1.valid = true) (level : (message.1.node message.1.bottom).level = depth) :
    MergeCorrect depth before (mergeMessage before message)
      (Multiset.replicate message.2 (decodeNode message.1 depth message.1.bottom)) := by
  let imported := importVista before.1 message.1
  let index := imported.2[message.1.bottom]?.getD 0
  let after := mergeMessage before message
  have inside : message.1.bottom < message.1.nodes.size := by
    simp only [Vista.valid, Bool.and_eq_true, decide_eq_true_eq] at valid
    exact valid.1.1.1
  have correct := importVista_correct before.1 message.1 (topological_of_valid _ valid)
  have bounded : index < imported.1.size := correct.2.2.1 message.1.bottom inside
  have nodeLevel : ((Vista.mk imported.1 0).node index).level = depth := by
    have h := congrArg Node.level (correct.2.2.2 message.1.bottom inside)
    simpa only [referenceMap, level] using h
  have wf : WellFormed ⟨imported.1, 0⟩ := importVista_wellFormed _ _ invariant.wellFormed
    (wellFormed_of_valid _ valid) (topological_of_valid _ valid)
  have incoming : IncomingAt depth after := by
    apply bundleKeys_addCount (fun i => i < imported.1.size ∧
      ((Vista.mk imported.1 0).node i).level = depth) index message.2 before.2
    · exact ⟨bounded, nodeLevel⟩
    · intro edge he
      obtain ⟨hei, hel⟩ := invariant.incomingAt edge he
      exact ⟨hei.trans_le correct.1, by rw [correct.2.1 edge.1 hei]; exact hel⟩
  refine ⟨⟨wf, importVista_baseClean _ _ invariant.baseClean (baseClean_of_valid _ valid),
    incoming⟩, correct.1, correct.2.1, ?_⟩
  change bundleMessages (decodeNode ⟨imported.1, 0⟩ depth)
    (addCount index message.2 before.2) = _
  rw [bundleMessages_addCount]
  have nodeHistory : decodeNode ⟨imported.1, 0⟩ depth index =
      decodeNode message.1 depth message.1.bottom := by
    have h := importVista_decode before.1 message.1 valid message.1.bottom inside
    rw [level] at h
    exact h
  rw [nodeHistory, bundleMessages_eq_of_extends depth before (imported.1, []) invariant correct.2.1]
  exact add_comm _ _

theorem MergeCorrect.trans {depth : Nat} {before middle after : MergeState}
    {first second : Multiset (Counting.FullHistory depth)}
    (left : MergeCorrect depth before middle first)
    (right : MergeCorrect depth middle after second) :
    MergeCorrect depth before after (first + second) := by
  refine ⟨right.invariant, left.size.trans right.size,
    left.extension.trans right.extension left.size, ?_⟩
  rw [right.messages, left.messages, add_assoc]

theorem mergeMessages_correct (depth : Nat) (received : List (Vista × Nat))
    (before : MergeState) (invariant : PoolInvariant depth before)
    (valid : ∀ message ∈ received, message.1.valid = true ∧
      (message.1.node message.1.bottom).level = depth) :
    MergeCorrect depth before (received.foldl mergeMessage before)
      (receivedHistories depth received) := by
  induction received generalizing before with
  | nil =>
      refine ⟨invariant, le_rfl, fun _ _ => rfl, ?_⟩
      simp [receivedHistories]
  | cons message rest ih =>
      obtain ⟨validMessage, messageLevel⟩ := valid message (by simp)
      have first := mergeMessage_correct depth before invariant message validMessage messageLevel
      have remaining := ih _ first.invariant (fun m hm => valid m (by simp [hm]))
      simpa only [List.foldl_cons, receivedHistories, List.map_cons, List.sum_cons] using
        first.trans remaining

theorem rawUpdate_correct (old : Vista) (received : List (Vista × Nat)) (outdegree : Nat)
    (valid : old.valid = true)
    (receivedValid : ∀ message ∈ received, message.1.valid = true ∧
      (message.1.node message.1.bottom).level = (old.node old.bottom).level) :
    WellFormed (rawUpdate old received outdegree) ∧
    BaseClean (rawUpdate old received outdegree) ∧
    ((rawUpdate old received outdegree).node (rawUpdate old received outdegree).bottom).level =
      (old.node old.bottom).level + 1 ∧
    decodeNode (rawUpdate old received outdegree) ((old.node old.bottom).level + 1)
      (rawUpdate old received outdegree).bottom =
      (old.denotes, outdegree, receivedHistories (old.node old.bottom).level received) := by
  let depth := (old.node old.bottom).level
  let start := importVista #[] old
  let ownBottom := start.2[old.bottom]?.getD 0
  let merged := received.foldl mergeMessage (start.1, [])
  let node : Node := ⟨depth + 1, some ownBottom, (old.node old.bottom).leader, outdegree, merged.2⟩
  let result : Vista := ⟨merged.1.push node, merged.1.size⟩
  have inside : old.bottom < old.nodes.size := by
    simp only [Vista.valid, Bool.and_eq_true, decide_eq_true_eq] at valid
    exact valid.1.1.1
  have imported := importVista_correct #[] old (topological_of_valid _ valid)
  have startWellFormed : WellFormed ⟨start.1, 0⟩ :=
    importVista_wellFormed #[] old (by intro i hi; simp at hi)
      (wellFormed_of_valid _ valid) (topological_of_valid _ valid)
  have startClean : BaseClean ⟨start.1, 0⟩ :=
    importVista_baseClean #[] old (by intro n hn; simp at hn) (baseClean_of_valid _ valid)
  have startInvariant : PoolInvariant depth (start.1, []) :=
    ⟨startWellFormed, startClean, by intro edge he; contradiction⟩
  have mergedCorrect := mergeMessages_correct depth received (start.1, []) startInvariant receivedValid
  have ownInside : ownBottom < start.1.size := imported.2.2.1 old.bottom inside
  have ownLevel : ((Vista.mk start.1 0).node ownBottom).level = depth := by
    simpa only [referenceMap] using congrArg Node.level (imported.2.2.2 old.bottom inside)
  have ownInsideMerged : ownBottom < merged.1.size := ownInside.trans_le mergedCorrect.size
  have ownLevelMerged : ((Vista.mk merged.1 0).node ownBottom).level = depth := by
    rw [mergedCorrect.extension ownBottom ownInside]
    exact ownLevel
  have ready : Ready ⟨merged.1, 0⟩ node := by
    right
    refine ⟨ownBottom, rfl, ownInsideMerged, ?_, ?_⟩
    · exact congrArg (· + 1) ownLevelMerged
    · intro edge he
      obtain ⟨hei, hel⟩ := mergedCorrect.invariant.incomingAt edge he
      exact ⟨hei, congrArg (· + 1) hel⟩
  have resultWellFormed : WellFormed result :=
    wellFormed_push ⟨merged.1, merged.1.size⟩ node mergedCorrect.invariant.wellFormed ready
  have resultClean : BaseClean result :=
    allNodes_push BaseCleanNode merged.1 node mergedCorrect.invariant.baseClean
      (by intro hz; simp only [node, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false] at hz)
  have resultLevel : (result.node result.bottom).level = depth + 1 := by
    rw [node_push_last]
  have extension : Extends ⟨merged.1, 0⟩ result := by
    intro i hi
    exact node_push_old _ _ _ _ hi
  have ownHistory : decodeNode result depth ownBottom = old.denotes := by
    have h1 := decodeNode_eq_of_extends ⟨merged.1, 0⟩ result mergedCorrect.invariant.wellFormed
      extension ownBottom ownInsideMerged
    rw [ownLevelMerged] at h1
    have h2 := decodeNode_eq_of_extends ⟨start.1, 0⟩ ⟨merged.1, 0⟩ startWellFormed
      mergedCorrect.extension ownBottom ownInside
    rw [ownLevel] at h2
    exact h1.trans (h2.trans (importVista_decode #[] old valid old.bottom inside))
  have incomingHistory : bundleMessages (decodeNode result depth) merged.2 =
      receivedHistories depth received := by
    have h := bundleMessages_eq_of_extends depth merged (result.nodes, [])
      mergedCorrect.invariant extension
    rw [decodeNode_bottom_irrel result.nodes 0 result.bottom depth] at h
    exact h.trans (by simpa only [bundleMessages_nil, zero_add] using mergedCorrect.messages)
  refine ⟨resultWellFormed, resultClean, resultLevel, ?_⟩
  change decodeNode result (depth + 1) result.bottom = _
  have resultNode : result.node result.bottom = node := node_push_last _ _ _
  simp only [decodeNode, resultNode, node, Option.getD_some]
  exact Prod.ext ownHistory (Prod.ext rfl incomingHistory)

theorem rawUpdate_bottom_lt (old : Vista) (received : List (Vista × Nat)) (outdegree : Nat) :
    (rawUpdate old received outdegree).bottom < (rawUpdate old received outdegree).nodes.size := by
  simp only [rawUpdate, Array.size_push, Nat.lt_add_one]

theorem updateVista_defined (old : Vista) (received : List (Vista × Nat)) (outdegree : Nat)
    (valid : old.valid = true)
    (receivedCheck : received.all (fun message => message.2 > 0 && message.1.valid &&
      (message.1.node message.1.bottom).level == (old.node old.bottom).level) = true) :
    updateVista? old received outdegree = some (canonicalize (rawUpdate old received outdegree)) := by
  simp only [updateVista?, valid, Bool.not_true, Bool.false_eq_true, if_false, receivedCheck,
    Option.pure_def, rawUpdate, mergeMessage_eq]

/-- A successful executable update uses exactly the simultaneous previous
histories, binary multiplicities and the newly learned outdegree. -/
theorem updateVista_sound (old : Vista) (received : List (Vista × Nat)) (outdegree : Nat)
    (next : Vista) (success : updateVista? old received outdegree = some next) :
    (next.node next.bottom).level = (old.node old.bottom).level + 1 ∧
    decodeNode next ((old.node old.bottom).level + 1) next.bottom =
      (old.denotes, outdegree, receivedHistories (old.node old.bottom).level received) := by
  have valid : old.valid = true := by
    cases hv : old.valid with
    | false => simp [updateVista?, hv] at success
    | true => rfl
  have receivedCheck : received.all (fun message => message.2 > 0 && message.1.valid &&
      (message.1.node message.1.bottom).level == (old.node old.bottom).level) = true := by
    cases hr : received.all (fun message => message.2 > 0 && message.1.valid &&
        (message.1.node message.1.bottom).level == (old.node old.bottom).level) with
    | false => simp [updateVista?, valid, hr] at success
    | true => rfl
  have receivedValid : ∀ message ∈ received, message.1.valid = true ∧
      (message.1.node message.1.bottom).level = (old.node old.bottom).level := by
    intro message hm
    have h := List.all_eq_true.mp receivedCheck message hm
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨h.1.2, h.2⟩
  have identify : next = canonicalize (rawUpdate old received outdegree) := by
    simpa only [updateVista?, valid, Bool.not_true, Bool.false_eq_true, if_false,
      receivedCheck, Option.pure_def, Option.some.injEq, rawUpdate, mergeMessage_eq] using success.symm
  subst next
  let source := rawUpdate old received outdegree
  have correct := rawUpdate_correct old received outdegree valid receivedValid
  have inside := rawUpdate_bottom_lt old received outdegree
  have relabels := canonicalize_relabels_of_references source
    (references_lower_of_structure source correct.1 correct.2.1)
  constructor
  · have h := congrArg Node.level (relabels source.bottom inside)
    rw [canonicalize_eq_fold]
    have hh : ((Vista.mk (canonicalState source).1 ((canonicalState source).2[source.bottom]?.getD 0)).node
        ((canonicalState source).2[source.bottom]?.getD 0)).level = (source.node source.bottom).level := by
      simpa only [referenceMap, canonicalize_eq_fold] using h
    exact hh.trans correct.2.2.1
  · have h := canonicalize_decode_of_structure source correct.1 correct.2.1 source.bottom inside
    rw [correct.2.2.1] at h
    simpa only [canonicalize_eq_fold] using h.trans correct.2.2.2

end Counting.Executable
