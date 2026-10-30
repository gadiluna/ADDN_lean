import Counting.DagSemanticsImport
import Mathlib.Data.List.Nodup

namespace Counting.Executable

abbrev CanonicalState := Array Node × Array Nat

def canonicalInsert (source : Vista) (state : CanonicalState) (index : Nat) : CanonicalState :=
  let next := intern state.1 (referenceMap state.2 (source.node index))
  (next.1, state.2.set! index next.2)

def canonicalLevel (source : Vista) (state : CanonicalState) (level : Nat) : CanonicalState :=
  let ordered := (levelNodes source level).mergeSort (fun i j =>
    lexLE (referenceMap state.2 (source.node i)).key
      (referenceMap state.2 (source.node j)).key)
  ordered.foldl (canonicalInsert source) state

def canonicalState (source : Vista) : CanonicalState :=
  (List.range (source.nodes.foldl (fun n node => max n node.level) 0 + 1)).foldl
    (canonicalLevel source) (#[], Array.replicate source.nodes.size 0)

/-- The fold presentation is exactly the existing executable loop, including
its state-dependent comparison order. No algorithm is replaced by a specification. -/
theorem canonicalize_eq_fold (source : Vista) :
    canonicalize source = ⟨(canonicalState source).1,
      (canonicalState source).2[source.bottom]?.getD 0⟩ := by
  simp only [canonicalize, List.forIn_pure_yield_eq_foldl, pure_bind]
  rfl

def ReferencesIn (node : Node) (done : Finset Nat) : Prop :=
  (∀ parent, node.parent = some parent → parent ∈ done) ∧
    ∀ edge ∈ node.incoming, edge.1 ∈ done

structure StateMaps (source : Vista) (done : Finset Nat) (state : CanonicalState) : Prop where
  mapSize : state.2.size = source.nodes.size
  inside : ∀ i ∈ done, i < source.nodes.size
  bounded : ∀ i ∈ done, state.2[i]?.getD 0 < state.1.size
  relabels : ∀ i ∈ done,
    (Vista.mk state.1 0).node (state.2[i]?.getD 0) = referenceMap state.2 (source.node i)
  closed : ∀ i ∈ done, ReferencesIn (source.node i) done

theorem referenceMap_set_ne (mapping : Array Nat) (index value : Nat) (node : Node)
    (parentNe : ∀ p, node.parent = some p → index ≠ p)
    (incomingNe : ∀ edge ∈ node.incoming, index ≠ edge.1) :
    referenceMap (mapping.set! index value) node = referenceMap mapping node := by
  apply referenceMap_congr
  · intro p hp
    simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds,
      if_neg (parentNe p hp)]
  · intro edge he
    simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds,
      if_neg (incomingNe edge he)]

theorem StateMaps.insert {source : Vista} {done : Finset Nat} {state : CanonicalState}
    (invariant : StateMaps source done state) (index : Nat)
    (inside : index < source.nodes.size) (fresh : index ∉ done)
    (references : ReferencesIn (source.node index) done) :
    StateMaps source (insert index done) (canonicalInsert source state index) := by
  let next := intern state.1 (referenceMap state.2 (source.node index))
  have mappingInside : index < state.2.size := by rw [invariant.mapSize]; exact inside
  have unchanged (i : Nat) (hi : i ∈ done) :
      (state.2.set! index next.2)[i]?.getD 0 = state.2[i]?.getD 0 := by
    have hne : index ≠ i := fun h => fresh (h ▸ hi)
    simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds, if_neg hne]
  have current : (state.2.set! index next.2)[index]?.getD 0 = next.2 := by
    simp [mappingInside]

  have referenceUnchanged (node : Node) (hn : ReferencesIn node done) :
      referenceMap (state.2.set! index next.2) node = referenceMap state.2 node := by
    apply referenceMap_set_ne
    · intro p hp h
      exact fresh (h ▸ hn.1 p hp)
    · intro edge he h
      exact fresh (h ▸ hn.2 edge he)
  constructor
  · simpa only [canonicalInsert, Array.set!_eq_setIfInBounds, Array.size_setIfInBounds] using
      invariant.mapSize
  · intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact inside
    · exact invariant.inside i hi
  · intro i hi
    change (state.2.set! index next.2)[i]?.getD 0 < next.1.size
    rcases Finset.mem_insert.mp hi with rfl | hi
    · rw [current]
      exact intern_index_lt _ _
    · rw [unchanged i hi]
      exact (invariant.bounded i hi).trans_le (intern_size_le _ _)
  · intro i hi
    change (Vista.mk next.1 0).node ((state.2.set! index next.2)[i]?.getD 0) =
      referenceMap (state.2.set! index next.2) (source.node i)
    rcases Finset.mem_insert.mp hi with rfl | hi
    · rw [current, referenceUnchanged _ references]
      exact intern_node _ _
    · rw [unchanged i hi, referenceUnchanged _ (invariant.closed i hi)]
      exact (intern_extends _ _ _ (invariant.bounded i hi)).trans (invariant.relabels i hi)
  · intro i hi
    have hin : ReferencesIn (source.node i) done := by
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact references
      · exact invariant.closed i hi
    exact ⟨fun p hp => Finset.mem_insert_of_mem (hin.1 p hp),
      fun edge he => Finset.mem_insert_of_mem (hin.2 edge he)⟩

theorem ReferencesIn.mono {node : Node} {left right : Finset Nat}
    (references : ReferencesIn node left) (included : left ⊆ right) : ReferencesIn node right :=
  ⟨fun p hp => included (references.1 p hp), fun edge he => included (references.2 edge he)⟩

/-- Any order within one level is sound: every dependency was already mapped
at an earlier level. This includes the executable signature-sorted order. -/
theorem StateMaps.fold_independent {source : Vista} (order : List Nat)
    (distinct : order.Nodup) {done : Finset Nat} {state : CanonicalState}
    (invariant : StateMaps source done state)
    (inside : ∀ i ∈ order, i < source.nodes.size)
    (fresh : ∀ i ∈ order, i ∉ done)
    (references : ∀ i ∈ order, ReferencesIn (source.node i) done) :
    StateMaps source (order.toFinset ∪ done) (order.foldl (canonicalInsert source) state) := by
  induction order generalizing done state with
  | nil => simpa using invariant
  | cons i rest ih =>
      obtain ⟨notMem, distinct⟩ := List.nodup_cons.mp distinct
      have next := invariant.insert i (inside i (by simp)) (fresh i (by simp))
        (references i (by simp))
      have result := ih distinct next
        (fun j hj => inside j (by simp [hj]))
        (by
          intro j hj h
          rcases Finset.mem_insert.mp h with h | h
          · exact notMem (h ▸ hj)
          · exact fresh j (by simp [hj]) h)
        (fun j hj => (references j (by simp [hj])).mono (Finset.subset_insert i done))
      simpa only [List.toFinset_cons, List.foldl_cons, Finset.insert_union,
        Finset.union_insert] using result

def lowerNodes (source : Vista) (level : Nat) : Finset Nat :=
  (Finset.range source.nodes.size).filter (fun i => (source.node i).level < level)

@[simp] theorem mem_lowerNodes (source : Vista) (level index : Nat) :
    index ∈ lowerNodes source level ↔ index < source.nodes.size ∧ (source.node index).level < level := by
  simp [lowerNodes]

@[simp] theorem lowerNodes_zero (source : Vista) : lowerNodes source 0 = ∅ := by
  simp [lowerNodes]

theorem lowerNodes_succ (source : Vista) (level : Nat) :
    lowerNodes source (level + 1) = (levelNodes source level).toFinset ∪ lowerNodes source level := by
  ext i
  simp only [mem_lowerNodes, Finset.mem_union, List.mem_toFinset, levelNodes,
    List.mem_filter, List.mem_range, beq_iff_eq]
  omega

theorem levelNodes_nodup (source : Vista) (level : Nat) :
    (levelNodes source level).Nodup := List.nodup_range.filter _

theorem references_lower_of_valid (source : Vista) (valid : source.valid = true)
    (index : Nat) (inside : index < source.nodes.size) :
    ReferencesIn (source.node index) (lowerNodes source (source.node index).level) := by
  have hn : nodeValid source index = true := by
    simp only [Vista.valid, Bool.and_eq_true] at valid
    exact List.all_eq_true.mp valid.1.1.2 index (List.mem_range.mpr inside)
  unfold nodeValid at hn
  dsimp only at hn
  by_cases hz : (source.node index).level = 0
  · simp only [beq_iff_eq, hz, if_true, Bool.and_eq_true,
      Option.isNone_iff_eq_none, List.isEmpty_iff] at hn
    constructor
    · intro parent hp
      rw [hn.1.1] at hp
      contradiction
    · intro edge he
      rw [hn.2] at he
      contradiction
  · obtain hzero | ⟨parent, hp, hpi, hpl, incoming⟩ := wellFormed_of_valid source valid index inside
    · exact False.elim (hz hzero)
    constructor
    · intro p hpp
      have heq : parent = p := Option.some.inj (hp.symm.trans hpp)
      subst p
      exact (mem_lowerNodes _ _ _).mpr ⟨hpi.trans inside, by omega⟩
    · intro edge he
      obtain ⟨hpi, hpl⟩ := incoming edge he
      exact (mem_lowerNodes _ _ _).mpr ⟨hpi.trans inside, by omega⟩

theorem StateMaps.level {source : Vista}
    (references : ∀ i, i < source.nodes.size →
      ReferencesIn (source.node i) (lowerNodes source (source.node i).level))
    (level : Nat) {state : CanonicalState}
    (invariant : StateMaps source (lowerNodes source level) state) :
    StateMaps source (lowerNodes source (level + 1)) (canonicalLevel source state level) := by
  let order := (levelNodes source level).mergeSort (fun i j =>
    lexLE (referenceMap state.2 (source.node i)).key (referenceMap state.2 (source.node j)).key)
  have member : ∀ i ∈ order, i < source.nodes.size ∧ (source.node i).level = level := by
    intro i hi
    simpa only [order, List.mem_mergeSort, levelNodes, List.mem_filter, List.mem_range,
      beq_iff_eq] using hi
  have result := invariant.fold_independent order ((levelNodes_nodup source level).mergeSort)
    (fun i hi => (member i hi).1)
    (by intro i hi hm; have a := member i hi; have b := (mem_lowerNodes _ _ _).mp hm; omega)
    (by
      intro i hi
      have h := references i (member i hi).1
      simpa only [(member i hi).2] using h)
  have orderSet : order.toFinset = (levelNodes source level).toFinset := by
    ext i
    simp only [List.mem_toFinset, order, List.mem_mergeSort]
  change StateMaps source (lowerNodes source (level + 1))
    (order.foldl (canonicalInsert source) state)
  simpa only [lowerNodes_succ, orderSet] using result

theorem canonicalState_prefix (source : Vista)
    (references : ∀ i, i < source.nodes.size →
      ReferencesIn (source.node i) (lowerNodes source (source.node i).level)) (levels : Nat) :
    StateMaps source (lowerNodes source levels)
      ((List.range levels).foldl (canonicalLevel source) (#[], Array.replicate source.nodes.size 0)) := by
  induction levels with
  | zero =>
      simp only [List.range_zero, List.foldl_nil, lowerNodes_zero]
      constructor
      · simp
      · simp
      · simp
      · simp
      · simp
  | succ levels ih =>
      simpa only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil] using
        ih.level references levels

theorem node_level_le_max (source : Vista) (index : Nat) (inside : index < source.nodes.size) :
    (source.node index).level ≤ source.nodes.foldl (fun n node => max n node.level) 0 := by
  have bounds : ∀ (nodes : List Node) (start : Nat),
      start ≤ nodes.foldl (fun n node => max n node.level) start ∧
      ∀ node ∈ nodes, node.level ≤ nodes.foldl (fun n node => max n node.level) start := by
    intro nodes
    induction nodes with
    | nil => intro start; simp
    | cons node rest ih =>
        intro start
        have next := ih (max start node.level)
        refine ⟨(le_max_left _ _).trans next.1, ?_⟩
        intro other h
        rcases List.mem_cons.mp h with rfl | h
        · exact (le_max_right _ _).trans next.1
        · exact next.2 other h
  have member : source.node index ∈ source.nodes.toList := by
    simp only [Vista.node, Array.getElem?_eq_getElem inside, Option.getD_some]
    exact Array.mem_toList_iff.mpr (Array.getElem_mem inside)
  simpa only [Array.foldl_toList] using (bounds source.nodes.toList 0).2 _ member

/-- The complete executable normalization maps every source node and preserves
its structural signature after references have been translated. -/
theorem canonicalState_correct_of_references (source : Vista)
    (references : ∀ i, i < source.nodes.size →
      ReferencesIn (source.node i) (lowerNodes source (source.node i).level)) :
    (canonicalState source).2.size = source.nodes.size ∧
    (∀ index, index < source.nodes.size →
      ((canonicalState source).2[index]?.getD 0) < (canonicalState source).1.size) ∧
    Relabels source ⟨(canonicalState source).1, 0⟩ (canonicalState source).2 := by
  have allMapped := canonicalState_prefix source references
    (source.nodes.foldl (fun n node => max n node.level) 0 + 1)
  have included (index : Nat) (inside : index < source.nodes.size) :
      index ∈ lowerNodes source (source.nodes.foldl (fun n node => max n node.level) 0 + 1) :=
    (mem_lowerNodes _ _ _).mpr ⟨inside, Nat.lt_succ_of_le (node_level_le_max source index inside)⟩
  exact ⟨allMapped.mapSize, fun i hi => allMapped.bounded i (included i hi),
    fun i hi => allMapped.relabels i (included i hi)⟩

theorem canonicalState_correct (source : Vista) (valid : source.valid = true) :
    (canonicalState source).2.size = source.nodes.size ∧
    (∀ index, index < source.nodes.size →
      ((canonicalState source).2[index]?.getD 0) < (canonicalState source).1.size) ∧
    Relabels source ⟨(canonicalState source).1, 0⟩ (canonicalState source).2 :=
  canonicalState_correct_of_references source (references_lower_of_valid source valid)

theorem canonicalize_relabels_of_references (source : Vista)
    (references : ∀ i, i < source.nodes.size →
      ReferencesIn (source.node i) (lowerNodes source (source.node i).level)) :
    Relabels source (canonicalize source) (canonicalState source).2 := by
  rw [canonicalize_eq_fold]
  exact (canonicalState_correct_of_references source references).2.2

theorem canonicalize_decode_of_references (source : Vista)
    (wellFormed : WellFormed source)
    (references : ∀ i, i < source.nodes.size →
      ReferencesIn (source.node i) (lowerNodes source (source.node i).level))
    (index : Nat) (inside : index < source.nodes.size) :
    decodeNode (canonicalize source) (source.node index).level
      ((canonicalState source).2[index]?.getD 0) = decodeNode source (source.node index).level index :=
  decodeNode_eq_of_relabels source _ _ wellFormed
    (canonicalize_relabels_of_references source references) index inside

theorem canonicalize_relabels (source : Vista) (valid : source.valid = true) :
    Relabels source (canonicalize source) (canonicalState source).2 := by
  rw [canonicalize_eq_fold]
  exact (canonicalState_correct source valid).2.2

/-- Every node's full-information history survives canonical normalization. -/
theorem canonicalize_decode (source : Vista) (valid : source.valid = true)
    (index : Nat) (inside : index < source.nodes.size) :
    decodeNode (canonicalize source) (source.node index).level
      ((canonicalState source).2[index]?.getD 0) = decodeNode source (source.node index).level index :=
  decodeNode_eq_of_relabels source _ _ (wellFormed_of_valid source valid)
    (canonicalize_relabels source valid) index inside

theorem canonicalize_bottom_level (source : Vista) (valid : source.valid = true) :
    ((canonicalize source).node (canonicalize source).bottom).level =
      (source.node source.bottom).level := by
  have inside : source.bottom < source.nodes.size := by
    simp only [Vista.valid, Bool.and_eq_true, decide_eq_true_eq] at valid
    exact valid.1.1.1
  have h := congrArg Node.level (canonicalize_relabels source valid source.bottom inside)
  simpa only [canonicalize_eq_fold, referenceMap] using h

theorem canonicalize_bottom_history (source : Vista) (valid : source.valid = true) :
    decodeNode (canonicalize source) (source.node source.bottom).level (canonicalize source).bottom =
      source.denotes := by
  have inside : source.bottom < source.nodes.size := by
    simp only [Vista.valid, Bool.and_eq_true, decide_eq_true_eq] at valid
    exact valid.1.1.1
  simpa only [canonicalize_eq_fold, Vista.denotes] using canonicalize_decode source valid source.bottom inside

end Counting.Executable
