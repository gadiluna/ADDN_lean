import Counting.DagSemanticsLabels

namespace Counting.Executable

def assignEntries (entries : List (Nat × Nat)) (weights : Array Nat) : Array Nat :=
  entries.foldl (fun state entry => state.set! entry.1 entry.2) weights

def propagateLevel (vista : Vista) (weights : Array Nat) (r : Nat) : Array Nat :=
  (levelNodes vista r).foldl (fun state node =>
    state.set! node ((children vista node (r + 1)).map (fun c => state[c]?.getD 0)).sum) weights

def propagateDown (vista : Vista) (bound : Nat) (weights : Array Nat) : Array Nat :=
  (List.range bound).reverse.foldl (propagateLevel vista) weights

theorem propagateWeights_eq_fold (vista : Vista) (anchor : Nat) (natural : Array Nat) :
    propagateWeights vista anchor natural =
      propagateDown vista anchor (assignEntries ((levelNodes vista anchor).zip natural.toList)
        (Array.replicate vista.nodes.size 0)) := by
  simp only [propagateWeights, List.forIn_pure_yield_eq_foldl, pure_bind]
  rfl

theorem assignEntries_size (entries : List (Nat × Nat)) (weights : Array Nat) :
    (assignEntries entries weights).size = weights.size := by
  induction entries generalizing weights with
  | nil => rfl
  | cons edge rest ih => exact (ih _).trans (by simp)

theorem assignEntries_unchanged (entries : List (Nat × Nat)) (weights : Array Nat) (key : Nat)
    (absent : ∀ edge ∈ entries, edge.1 ≠ key) :
    (assignEntries entries weights)[key]?.getD 0 = weights[key]?.getD 0 := by
  induction entries generalizing weights with
  | nil => rfl
  | cons edge rest ih =>
      change (assignEntries rest (weights.set! edge.1 edge.2))[key]?.getD 0 = _
      rw [ih _ (fun e he => absent e (by simp [he]))]
      simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds,
        if_neg (absent edge (by simp))]

theorem assignEntries_entry (entries : List (Nat × Nat)) (weights : Array Nat)
    (distinct : (entries.map Prod.fst).Nodup) (key value : Nat)
    (present : (key, value) ∈ entries) (inside : key < weights.size) :
    (assignEntries entries weights)[key]?.getD 0 = value := by
  induction entries generalizing weights with
  | nil => contradiction
  | cons edge rest ih =>
      obtain ⟨notMem, tailDistinct⟩ := List.nodup_cons.mp distinct
      rcases List.mem_cons.mp present with rfl | present
      · change (assignEntries rest (weights.set! key value))[key]?.getD 0 = _
        rw [assignEntries_unchanged rest _ key (by
          intro e he equal
          exact notMem (List.mem_map.mpr ⟨e, he, equal⟩))]
        simp [inside]
      · exact ih _ tailDistinct present (by simpa using inside)

theorem mem_levelNodes (vista : Vista) (r i : Nat) :
    i ∈ levelNodes vista r ↔ i < vista.nodes.size ∧ (vista.node i).level = r := by
  simp only [levelNodes, List.mem_filter, List.mem_range, beq_iff_eq]

theorem child_level (vista : Vista) (parent r child : Nat) (member : child ∈ children vista parent r) :
    child < vista.nodes.size ∧ (vista.node child).level = r := by
  have h := (List.mem_filter.mp member).1
  exact (mem_levelNodes vista r child).mp h

theorem assign_anchor_coordinate (vista : Vista) (anchor : Nat) (natural : Array Nat)
    (size : natural.size = (levelNodes vista anchor).length)
    (j : Fin (levelNodes vista anchor).length) :
    (assignEntries ((levelNodes vista anchor).zip natural.toList)
      (Array.replicate vista.nodes.size 0))[(levelNodes vista anchor)[j.val]]?.getD 0 =
      natural[j.val]?.getD 0 := by
  have naturalInside : j.val < natural.size := by rw [size]; exact j.isLt
  have distinct : (((levelNodes vista anchor).zip natural.toList).map Prod.fst).Nodup := by
    rw [List.map_fst_zip]
    · exact levelNodes_nodup vista anchor
    · simpa only [Array.length_toList, size] using le_refl (levelNodes vista anchor).length
  have pairInside : j.val < ((levelNodes vista anchor).zip natural.toList).length := by
    simpa only [List.length_zip, Array.length_toList, size, min_self] using j.isLt
  have pairMem := List.getElem_mem pairInside
  have pair : ((levelNodes vista anchor)[j.val], natural[j.val]?.getD 0) ∈
      (levelNodes vista anchor).zip natural.toList := by
    simpa only [List.getElem_zip, Array.getElem_toList, Array.getElem?_eq_getElem naturalInside,
      Option.getD_some] using pairMem
  apply assignEntries_entry _ _ distinct _ _ pair
  simpa only [Array.size_replicate] using
    ((mem_levelNodes vista anchor _).mp (List.getElem_mem j.isLt)).1

def updateNodes (vista : Vista) (r : Nat) (nodes : List Nat) (weights : Array Nat) : Array Nat :=
  nodes.foldl (fun state node =>
    state.set! node ((children vista node (r + 1)).map (fun c => state[c]?.getD 0)).sum) weights

theorem updateNodes_size (vista : Vista) (r : Nat) (nodes : List Nat) (weights : Array Nat) :
    (updateNodes vista r nodes weights).size = weights.size := by
  induction nodes generalizing weights with
  | nil => rfl
  | cons i rest ih => exact (ih _).trans (by simp)

theorem updateNodes_unchanged (vista : Vista) (r : Nat) (nodes : List Nat)
    (weights : Array Nat) (key : Nat) (absent : key ∉ nodes) :
    (updateNodes vista r nodes weights)[key]?.getD 0 = weights[key]?.getD 0 := by
  induction nodes generalizing weights with
  | nil => rfl
  | cons i rest ih =>
      have unequal : i ≠ key := by intro h; apply absent; simp [h]
      have tail : key ∉ rest := fun h => absent (by simp [h])
      change (updateNodes vista r rest (weights.set! i _))[key]?.getD 0 = _
      rw [ih _ tail]
      simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds, if_neg unequal]

theorem updateNodes_entry (vista : Vista) (r : Nat) (nodes : List Nat) (weights : Array Nat)
    (size : weights.size = vista.nodes.size) (distinct : nodes.Nodup)
    (atLevel : ∀ i ∈ nodes, i ∈ levelNodes vista r) (key : Nat) (present : key ∈ nodes) :
    (updateNodes vista r nodes weights)[key]?.getD 0 =
      ((children vista key (r + 1)).map (fun c => weights[c]?.getD 0)).sum := by
  induction nodes generalizing weights with
  | nil => contradiction
  | cons i rest ih =>
      obtain ⟨notMem, tailDistinct⟩ := List.nodup_cons.mp distinct
      have iLevel := (mem_levelNodes vista r i).mp (atLevel i (by simp))
      rcases List.mem_cons.mp present with rfl | present
      · change (updateNodes vista r rest (weights.set! key _))[key]?.getD 0 = _
        rw [updateNodes_unchanged vista r rest _ key notMem]
        have inside : key < weights.size := by rw [size]; exact iLevel.1
        simp [inside]
      · change (updateNodes vista r rest (weights.set! i _))[key]?.getD 0 = _
        rw [ih _ (by simpa using size) tailDistinct (fun j hj => atLevel j (by simp [hj])) present]
        apply congrArg List.sum
        apply List.map_congr_left
        intro child hc
        have childLevel := (child_level vista key (r + 1) child hc).2
        have unequal : i ≠ child := by intro h; subst child; omega
        simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds, if_neg unequal]

theorem propagateLevel_size (vista : Vista) (r : Nat) (weights : Array Nat) :
    (propagateLevel vista weights r).size = weights.size :=
  updateNodes_size vista r (levelNodes vista r) weights

theorem propagateLevel_unchanged (vista : Vista) (r : Nat) (weights : Array Nat) (key : Nat)
    (different : (vista.node key).level ≠ r) :
    (propagateLevel vista weights r)[key]?.getD 0 = weights[key]?.getD 0 := by
  apply updateNodes_unchanged vista r (levelNodes vista r) weights key
  intro h
  exact different ((mem_levelNodes vista r key).mp h).2

theorem propagateLevel_entry (vista : Vista) (r : Nat) (weights : Array Nat)
    (size : weights.size = vista.nodes.size) (key : Nat) (present : key ∈ levelNodes vista r) :
    (propagateLevel vista weights r)[key]?.getD 0 =
      ((children vista key (r + 1)).map (fun c => weights[c]?.getD 0)).sum :=
  updateNodes_entry vista r (levelNodes vista r) weights size (levelNodes_nodup vista r)
    (fun _ h => h) key present

theorem propagateDown_succ (vista : Vista) (bound : Nat) (weights : Array Nat) :
    propagateDown vista (bound + 1) weights =
      propagateDown vista bound (propagateLevel vista weights bound) := by
  simp only [propagateDown, List.range_succ, List.reverse_append, List.reverse_singleton,
    List.singleton_append, List.foldl_cons]

theorem propagateDown_size (vista : Vista) (bound : Nat) (weights : Array Nat) :
    (propagateDown vista bound weights).size = weights.size := by
  induction bound generalizing weights with
  | zero => rfl
  | succ bound ih => rw [propagateDown_succ, ih, propagateLevel_size]

theorem propagateDown_unchanged (vista : Vista) (bound : Nat) (weights : Array Nat) (key : Nat)
    (above : bound ≤ (vista.node key).level) :
    (propagateDown vista bound weights)[key]?.getD 0 = weights[key]?.getD 0 := by
  induction bound generalizing weights with
  | zero => rfl
  | succ bound ih =>
      rw [propagateDown_succ, ih _ (by omega), propagateLevel_unchanged vista bound weights key (by omega)]

/-- The actual descending loop enforces every backward equation. Writes
at lower levels cannot change the children used by an already audited row. -/
theorem propagateDown_backward (vista : Vista) (bound : Nat) (weights : Array Nat)
    (size : weights.size = vista.nodes.size) (r : Nat) (below : r < bound)
    (key : Nat) (present : key ∈ levelNodes vista r) :
    (propagateDown vista bound weights)[key]?.getD 0 =
      ((children vista key (r + 1)).map
        (fun c => (propagateDown vista bound weights)[c]?.getD 0)).sum := by
  induction bound generalizing weights r with
  | zero => omega
  | succ bound ih =>
      rw [propagateDown_succ]
      rcases lt_or_eq_of_le (Nat.le_of_lt_succ below) with less | equal
      · exact ih _ ((propagateLevel_size vista bound weights).trans size) r less present
      · subst r
        have keyLevel := (mem_levelNodes vista bound key).mp present
        rw [propagateDown_unchanged vista bound _ key (by omega),
          propagateLevel_entry vista bound weights size key present]
        apply congrArg List.sum
        apply List.map_congr_left
        intro child hc
        have childLevel := (child_level vista key (bound + 1) child hc).2
        rw [propagateDown_unchanged vista bound _ child (by omega),
          propagateLevel_unchanged vista bound weights child (by omega)]

theorem propagateWeights_size (vista : Vista) (anchor : Nat) (natural : Array Nat) :
    (propagateWeights vista anchor natural).size = vista.nodes.size := by
  rw [propagateWeights_eq_fold, propagateDown_size, assignEntries_size, Array.size_replicate]

theorem propagateWeights_anchor (vista : Vista) (anchor : Nat) (natural : Array Nat)
    (size : natural.size = (levelNodes vista anchor).length)
    (j : Fin (levelNodes vista anchor).length) :
    (propagateWeights vista anchor natural)[(levelNodes vista anchor)[j.val]]?.getD 0 =
      natural[j.val]?.getD 0 := by
  rw [propagateWeights_eq_fold, propagateDown_unchanged]
  · exact assign_anchor_coordinate vista anchor natural size j
  · exact le_of_eq ((mem_levelNodes vista anchor _).mp (List.getElem_mem j.isLt)).2.symm

theorem propagateWeights_backward (vista : Vista) (anchor : Nat) (natural : Array Nat)
    (r : Nat) (below : r < anchor) (key : Nat) (present : key ∈ levelNodes vista r) :
    (propagateWeights vista anchor natural)[key]?.getD 0 =
      ((children vista key (r + 1)).map
        (fun c => (propagateWeights vista anchor natural)[c]?.getD 0)).sum := by
  rw [propagateWeights_eq_fold]
  exact propagateDown_backward vista anchor _
    (by rw [assignEntries_size, Array.size_replicate]) r below key present

end Counting.Executable
