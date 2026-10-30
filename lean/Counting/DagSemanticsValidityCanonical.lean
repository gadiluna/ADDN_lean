import Counting.DagSemanticsValidityNodes
import Counting.DagSemanticsValidityClosure
import Counting.DagSemanticsVisibility

namespace Counting.Executable

/-- Every normalized node is the image of an already processed source node. -/
def StateCovered (done : Finset Nat) (state : CanonicalState) : Prop :=
  ∀ j, j < state.1.size → ∃ i ∈ done, state.2[i]?.getD 0 = j

structure SafeState (source : Vista) (done : Finset Nat) (state : CanonicalState) : Prop
    extends StateMaps source done state where
  validNodes : NodesValid ⟨state.1, 0⟩
  distinct : state.1.toList.Nodup
  covered : StateCovered done state

theorem StateMaps.nodeReady {source : Vista} {done : Finset Nat} {state : CanonicalState}
    (invariant : StateMaps source done state) (i : Nat) (inside : i < source.nodes.size)
    (valid : nodeValid source i = true) (references : ReferencesIn (source.node i) done) :
    NodeReady ⟨state.1, 0⟩ (referenceMap state.2 (source.node i)) := by
  have fields (j : Nat) (hj : j ∈ done) :
      ((Vista.mk state.1 0).node (state.2[j]?.getD 0)).level = (source.node j).level ∧
      ((Vista.mk state.1 0).node (state.2[j]?.getD 0)).leader = (source.node j).leader := by
    rw [invariant.relabels j hj]
    exact ⟨rfl, rfl⟩
  rcases nodeReady_of_check source i inside valid with ⟨zero, parent, degree, incoming⟩ |
      ⟨positive, p, hp, _, level, leader, _, incoming⟩
  · left
    simp only [referenceMap, zero, parent, degree, incoming, Option.map_none, List.foldl_nil, and_self]
  · right
    have pdone := references.1 p hp
    refine ⟨positive, state.2[p]?.getD 0, by simp only [referenceMap, hp, Option.map_some],
      invariant.bounded p pdone, ?_, ?_, referenceMap_countsSorted _ _, ?_⟩
    · exact (congrArg (· + 1) (fields p pdone).1).trans level
    · exact (fields p pdone).2.trans leader
    · apply referenceMap_keys (fun j => j < state.1.size ∧
        ((Vista.mk state.1 0).node j).level + 1 = (source.node i).level)
      intro e he
      have edone := references.2 e he
      exact ⟨invariant.bounded e.1 edone,
        (congrArg (· + 1) (fields e.1 edone).1).trans (incoming e he).2⟩

theorem SafeState.insert {source : Vista} {done : Finset Nat} {state : CanonicalState}
    (invariant : SafeState source done state) (index : Nat)
    (inside : index < source.nodes.size) (fresh : index ∉ done)
    (valid : nodeValid source index = true)
    (references : ReferencesIn (source.node index) done) :
    SafeState source (insert index done) (canonicalInsert source state index) := by
  let next := intern state.1 (referenceMap state.2 (source.node index))
  have mapInside : index < state.2.size := by rw [invariant.mapSize]; exact inside
  refine ⟨invariant.toStateMaps.insert index inside fresh references,
    intern_nodesValid _ _ invariant.validNodes
      (invariant.toStateMaps.nodeReady index inside valid references),
    intern_nodup _ _ invariant.distinct, ?_⟩
  intro j hj
  change j < next.1.size at hj
  change ∃ i ∈ Insert.insert index done, (state.2.set! index next.2)[i]?.getD 0 = j
  by_cases old : j < state.1.size
  · obtain ⟨i, hi, equal⟩ := invariant.covered j old
    refine ⟨i, Finset.mem_insert_of_mem hi, ?_⟩
    have neq : index ≠ i := fun eq => fresh (eq ▸ hi)
    simpa only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds, if_neg neq] using equal
  · have equal : next.2 = j := by
      dsimp only [next] at hj ⊢
      unfold intern at hj ⊢
      split at hj <;> rename_i found
      · exact False.elim (old hj)
      · simp only [Array.size_push] at hj
        omega
    exact ⟨index, Finset.mem_insert_self _ _, by simp [mapInside, equal]⟩

theorem SafeState.fold_independent {source : Vista} (order : List Nat)
    (distinct : order.Nodup) {done : Finset Nat} {state : CanonicalState}
    (invariant : SafeState source done state)
    (inside : ∀ i ∈ order, i < source.nodes.size)
    (fresh : ∀ i ∈ order, i ∉ done)
    (valid : ∀ i ∈ order, nodeValid source i = true)
    (references : ∀ i ∈ order, ReferencesIn (source.node i) done) :
    SafeState source (order.toFinset ∪ done) (order.foldl (canonicalInsert source) state) := by
  induction order generalizing done state with
  | nil => simpa using invariant
  | cons i rest ih =>
      obtain ⟨notMem, distinct⟩ := List.nodup_cons.mp distinct
      have next := invariant.insert i (inside i (by simp)) (fresh i (by simp))
        (valid i (by simp)) (references i (by simp))
      have result := ih distinct next
        (fun j hj => inside j (by simp [hj]))
        (by
          intro j hj h
          rcases Finset.mem_insert.mp h with h | h
          · exact notMem (h ▸ hj)
          · exact fresh j (by simp [hj]) h)
        (fun j hj => valid j (by simp [hj]))
        (fun j hj => (references j (by simp [hj])).mono (Finset.subset_insert i done))
      simpa only [List.toFinset_cons, List.foldl_cons, Finset.insert_union,
        Finset.union_insert] using result

theorem SafeState.level {source : Vista} (valid : NodesValid source)
    (level : Nat) {state : CanonicalState}
    (invariant : SafeState source (lowerNodes source level) state) :
    SafeState source (lowerNodes source (level + 1)) (canonicalLevel source state level) := by
  let order := (levelNodes source level).mergeSort (fun i j =>
    lexLE (referenceMap state.2 (source.node i)).key (referenceMap state.2 (source.node j)).key)
  have member : ∀ i ∈ order, i < source.nodes.size ∧ (source.node i).level = level := by
    intro i hi
    simpa only [order, List.mem_mergeSort, levelNodes, List.mem_filter, List.mem_range,
      beq_iff_eq] using hi
  have result := invariant.fold_independent order ((levelNodes_nodup source level).mergeSort)
    (fun i hi => (member i hi).1)
    (by intro i hi hm; have a := member i hi; have b := (mem_lowerNodes _ _ _).mp hm; omega)
    (fun i hi => valid i (member i hi).1)
    (by
      intro i hi
      have h := nodesValid_references source valid i (member i hi).1
      simpa only [(member i hi).2] using h)
  have orderSet : order.toFinset = (levelNodes source level).toFinset := by
    ext i
    simp only [List.mem_toFinset, order, List.mem_mergeSort]
  change SafeState source (lowerNodes source (level + 1))
    (order.foldl (canonicalInsert source) state)
  simpa only [lowerNodes_succ, orderSet] using result

theorem canonicalState_safe (source : Vista) (valid : NodesValid source) :
    SafeState source
      (lowerNodes source (source.nodes.foldl (fun n node => max n node.level) 0 + 1))
      (canonicalState source) := by
  have prefixInvariant (levels : Nat) : SafeState source (lowerNodes source levels)
      ((List.range levels).foldl (canonicalLevel source) (#[], Array.replicate source.nodes.size 0)) := by
    induction levels with
    | zero =>
        simp only [List.range_zero, List.foldl_nil, lowerNodes_zero]
        refine ⟨?_, ?_, by simp, ?_⟩
        · exact ⟨by simp, by simp, by simp, by simp, by simp⟩
        · intro i hi; simp at hi
        · intro j hj; simp at hj
    | succ levels ih =>
        simpa only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil] using
          ih.level valid levels
  exact prefixInvariant _

theorem canonicalize_nodesValid (source : Vista) (valid : NodesValid source) :
    NodesValid (canonicalize source) := by
  rw [canonicalize_eq_fold]
  exact (canonicalState_safe source valid).validNodes

theorem canonicalize_nodup (source : Vista) (valid : NodesValid source) :
    (canonicalize source).nodes.toList.Nodup := by
  rw [canonicalize_eq_fold]
  exact (canonicalState_safe source valid).distinct

theorem canonicalize_covered (source : Vista) (valid : NodesValid source)
    (j : Nat) (inside : j < (canonicalize source).nodes.size) :
    ∃ i, i < source.nodes.size ∧ (canonicalState source).2[i]?.getD 0 = j := by
  rw [canonicalize_eq_fold] at inside
  obtain ⟨i, hi, equal⟩ := (canonicalState_safe source valid).covered j inside
  exact ⟨i, ((mem_lowerNodes _ _ _).mp hi).1, equal⟩

theorem referenceMap_incoming_mem (mapping : Array Nat) (node : Node)
    (edge : Nat × Nat) (member : edge ∈ node.incoming) (positive : 0 < edge.2) :
    ∃ mapped ∈ (referenceMap mapping node).incoming, mapped.1 = mapping[edge.1]?.getD 0 := by
  have occurs : mapping[edge.1]?.getD 0 ∈ bundleMessages id (referenceMap mapping node).incoming := by
    rw [bundleMessages_referenceMap]
    exact (mem_bundleMessages _ _ _).mpr ⟨edge, member, positive, rfl⟩
  obtain ⟨mapped, hm, _, equal⟩ := (mem_bundleMessages _ _ _).mp occurs
  exact ⟨mapped, hm, equal⟩

theorem DagReach.relabels {source target : Vista} (mapping : Array Nat)
    (valid : NodesValid source) (relabels : Relabels source target mapping)
    (bounded : ∀ i, i < source.nodes.size → mapping[i]?.getD 0 < target.nodes.size)
    {a b : Nat} (reach : DagReach source a b) :
    DagReach target (mapping[a]?.getD 0) (mapping[b]?.getD 0) := by
  induction reach with
  | root => exact .root
  | @parent i p _ inside parent ih =>
      apply ih.parent (bounded i inside)
      rw [relabels i inside]
      simp only [referenceMap, parent, Option.map_some]
  | @incoming i edge _ inside incoming ih =>
      have nonzero : (source.node i).level ≠ 0 := by
        intro zero
        have empty := (nodeValid_zero source i (valid i inside) zero).2.2
        rw [empty] at incoming
        contradiction
      obtain ⟨_, _, _, _, _, sorted, _⟩ := nodeValid_positive source i (valid i inside) nonzero
      have positive := (sparse_of_countsSorted _ sorted).2 edge incoming
      obtain ⟨mapped, hm, equal⟩ := referenceMap_incoming_mem mapping (source.node i) edge incoming positive
      rw [← equal]
      apply ih.incoming (bounded i inside)
      rw [relabels i inside]
      exact hm

theorem canonicalize_allReachable (source : Vista) (valid : NodesValid source)
    (reachable : AllReachable source) : AllReachable (canonicalize source) := by
  have correct := canonicalState_correct_of_references source (nodesValid_references source valid)
  have relabels := canonicalize_relabels_of_references source (nodesValid_references source valid)
  intro j hj
  obtain ⟨i, hi, equal⟩ := canonicalize_covered source valid j hj
  have result := (reachable i hi).relabels (canonicalState source).2 valid relabels (by simpa only [canonicalize_eq_fold] using correct.2.1)
  simpa only [canonicalize_eq_fold, equal] using result

theorem eraseDups_eq_of_nodup {α : Type} [BEq α] [LawfulBEq α]
    (list : List α) (distinct : list.Nodup) : list.eraseDups = list := by
  induction list with
  | nil => rfl
  | cons a rest ih =>
      obtain ⟨absent, tail⟩ := List.nodup_cons.mp distinct
      have filtered : rest.filter (fun b => !b == a) = rest := by
        apply List.filter_eq_self.mpr
        intro b hb
        have neq : b ≠ a := by intro equal; exact absent (equal ▸ hb)
        simp [neq]
      rw [List.eraseDups_cons, filtered, ih tail]

theorem valid_of_properties (vista : Vista) (inside : vista.bottom < vista.nodes.size)
    (valid : NodesValid vista) (distinct : vista.nodes.toList.Nodup) (reachable : AllReachable vista) :
    vista.valid = true := by
  have nodup : vista.nodes.toList.eraseDups.length = vista.nodes.size := by
    rw [eraseDups_eq_of_nodup _ distinct]
    exact Array.length_toList
  simp only [Vista.valid, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  exact ⟨⟨⟨inside, List.all_eq_true.mpr (fun i hi => valid i (List.mem_range.mp hi))⟩, nodup⟩,
    closure_complete vista (nodesValid_topological vista valid) inside reachable⟩

theorem canonicalize_valid_of_properties (source : Vista)
    (inside : source.bottom < source.nodes.size) (valid : NodesValid source)
    (reachable : AllReachable source) : (canonicalize source).valid = true := by
  apply valid_of_properties _ _ (canonicalize_nodesValid source valid)
    (canonicalize_nodup source valid) (canonicalize_allReachable source valid reachable)
  rw [canonicalize_eq_fold]
  exact (canonicalState_correct_of_references source (nodesValid_references source valid)).2.1 _ inside

theorem canonicalize_valid (source : Vista) (valid : source.valid = true) :
    (canonicalize source).valid = true := by
  apply canonicalize_valid_of_properties source _ (nodesValid_of_valid source valid)
    (allReachable_of_valid source valid)
  simp only [Vista.valid, Bool.and_eq_true, decide_eq_true_eq] at valid
  exact valid.1.1.1

end Counting.Executable
