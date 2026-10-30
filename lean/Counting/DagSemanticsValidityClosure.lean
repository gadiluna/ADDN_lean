import Counting.DagSemanticsClosure

namespace Counting.Executable

/-- Reachability follows stored parent and red references backwards from a node. -/
inductive DagReach (vista : Vista) (root : Nat) : Nat → Prop
  | root : DagReach vista root root
  | parent {i p} : DagReach vista root i → i < vista.nodes.size →
      (vista.node i).parent = some p → DagReach vista root p
  | incoming {i edge} : DagReach vista root i → i < vista.nodes.size →
      edge ∈ (vista.node i).incoming → DagReach vista root edge.1

def AllReachable (vista : Vista) : Prop :=
  ∀ i, i < vista.nodes.size → DagReach vista vista.bottom i

theorem allReachable_of_valid (vista : Vista) (valid : vista.valid = true) : AllReachable vista :=
  valid_nodes_induction vista valid (DagReach vista vista.bottom) DagReach.root
    (fun _ hi reached _ hp => reached.parent hi hp)
    (fun _ hi reached _ he => reached.incoming hi he)

theorem DagReach.trans {vista : Vista} {a b c : Nat}
    (first : DagReach vista a b) (second : DagReach vista b c) : DagReach vista a c := by
  induction second with
  | root => exact first
  | parent _ inside parent ih => exact ih.parent inside parent
  | incoming _ inside incoming ih => exact ih.incoming inside incoming

theorem DagReach.extends {source target : Vista} (extension : Extends source target)
    (size : source.nodes.size ≤ target.nodes.size) {a b : Nat}
    (reach : DagReach source a b) : DagReach target a b := by
  induction reach with
  | root => exact .root
  | parent _ inside parent ih =>
      exact ih.parent (inside.trans_le size) (by rw [extension _ inside]; exact parent)
  | incoming _ inside incoming ih =>
      exact ih.incoming (inside.trans_le size) (by rw [extension _ inside]; exact incoming)

/-- Setting additional flags never clears an already marked node. -/
def FlagsLE (left right : Array Bool) : Prop :=
  ∀ i : Nat, left[i]?.getD false = true → right[i]?.getD false = true

theorem FlagsLE.refl (seen : Array Bool) : FlagsLE seen seen := fun _ h => h

theorem FlagsLE.trans {a b c : Array Bool} (ab : FlagsLE a b) (bc : FlagsLE b c) : FlagsLE a c :=
  fun i h => bc i (ab i h)

theorem flagsLE_set (seen : Array Bool) (index : Nat) : FlagsLE seen (seen.set! index true) := by
  intro i hi
  by_cases eq : index = i
  · subst index
    have inside : i < seen.size := by
      by_contra h
      simp only [Array.getElem?_eq_none (Nat.le_of_not_gt h), Option.getD_none] at hi
      contradiction
    simp [inside]
  · simpa only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds, if_neg eq] using hi

theorem markIncoming_monotone (seen : Array Bool) (incoming : List (Nat × Nat)) :
    FlagsLE seen (markIncoming seen incoming) := by
  induction incoming generalizing seen with
  | nil => exact .refl seen
  | cons edge rest ih => exact (flagsLE_set seen edge.1).trans (ih _)

theorem markIncoming_marks (seen : Array Bool) (incoming : List (Nat × Nat))
    (edge : Nat × Nat) (member : edge ∈ incoming) (inside : edge.1 < seen.size) :
    (markIncoming seen incoming)[edge.1]?.getD false = true := by
  induction incoming generalizing seen with
  | nil => contradiction
  | cons first rest ih =>
      rcases List.mem_cons.mp member with equal | member
      · subst edge
        exact markIncoming_monotone (seen.set! first.1 true) rest first.1 (by simp [inside])
      · exact ih _ member (by simpa using inside)

theorem closeNode_monotone (vista : Vista) (seen : Array Bool) (i : Nat) :
    FlagsLE seen (closeNode vista seen i) := by
  unfold closeNode
  split
  · dsimp only
    cases hp : (vista.node i).parent with
    | none => exact markIncoming_monotone seen _
    | some p => exact (flagsLE_set seen p).trans (markIncoming_monotone _ _)
  · exact .refl seen

theorem closeNode_parent (vista : Vista) (seen : Array Bool) (i p : Nat)
    (marked : seen[i]?.getD false = true) (parent : (vista.node i).parent = some p)
    (inside : p < seen.size) : (closeNode vista seen i)[p]?.getD false = true := by
  simp only [closeNode, marked, if_true, parent]
  exact markIncoming_monotone (seen.set! p true) _ p (by simp [inside])

theorem closeNode_incoming (vista : Vista) (seen : Array Bool) (i : Nat) (edge : Nat × Nat)
    (marked : seen[i]?.getD false = true) (member : edge ∈ (vista.node i).incoming)
    (inside : edge.1 < seen.size) : (closeNode vista seen i)[edge.1]?.getD false = true := by
  simp only [closeNode, marked, if_true]
  apply markIncoming_marks _ _ edge member
  cases (vista.node i).parent <;> simpa using inside

def closurePass (vista : Vista) (seen : Array Bool) : Array Bool :=
  (List.range vista.nodes.size).foldl (closeNode vista) seen

def closurePasses (vista : Vista) : Nat → Array Bool
  | 0 => (Array.replicate vista.nodes.size false).set! vista.bottom true
  | n+1 => closurePass vista (closurePasses vista n)

theorem closeNodes_monotone (vista : Vista) (order : List Nat) (seen : Array Bool) :
    FlagsLE seen (order.foldl (closeNode vista) seen) := by
  induction order generalizing seen with
  | nil => exact .refl seen
  | cons i rest ih => exact (closeNode_monotone vista seen i).trans (ih _)

theorem closeNodes_size (vista : Vista) (order : List Nat) (seen : Array Bool) :
    (order.foldl (closeNode vista) seen).size = seen.size := by
  induction order generalizing seen with
  | nil => rfl
  | cons i rest ih => exact (ih _).trans (closeNode_size vista seen i)

theorem closeNodes_step (vista : Vista) (order : List Nat) (seen : Array Bool)
    (i : Nat) (member : i ∈ order) (marked : seen[i]?.getD false = true)
    (p : Nat) (inside : p < seen.size)
    (reference : (vista.node i).parent = some p ∨ ∃ edge ∈ (vista.node i).incoming, edge.1 = p) :
    (order.foldl (closeNode vista) seen)[p]?.getD false = true := by
  induction order generalizing seen with
  | nil => contradiction
  | cons first rest ih =>
      rcases List.mem_cons.mp member with equal | member
      · subst i
        apply closeNodes_monotone vista rest (closeNode vista seen first) p
        rcases reference with parent | ⟨edge, he, rfl⟩
        · exact closeNode_parent vista seen first p marked parent inside
        · exact closeNode_incoming vista seen first edge marked he inside
      · exact ih _ member (closeNode_monotone vista seen first i marked)
          (by simpa only [closeNode_size] using inside)

theorem closurePasses_size (vista : Vista) (n : Nat) :
    (closurePasses vista n).size = vista.nodes.size := by
  induction n with
  | zero => simp [closurePasses]
  | succ n ih => exact (closeNodes_size _ _ _).trans ih

theorem closurePasses_mono (vista : Vista) (n m : Nat) (le : n ≤ m) :
    FlagsLE (closurePasses vista n) (closurePasses vista m) := by
  induction m, le using Nat.le_induction with
  | base => exact .refl _
  | succ m _ ih => exact ih.trans (closeNodes_monotone vista _ _)

theorem closurePasses_step (vista : Vista) (n i p : Nat)
    (inside : i < vista.nodes.size) (targetInside : p < vista.nodes.size)
    (marked : (closurePasses vista n)[i]?.getD false = true)
    (reference : (vista.node i).parent = some p ∨ ∃ edge ∈ (vista.node i).incoming, edge.1 = p) :
    (closurePasses vista (n+1))[p]?.getD false = true :=
  closeNodes_step vista _ _ i (List.mem_range.mpr inside) marked p
    (by simpa only [closurePasses_size] using targetInside) reference

theorem closure_eq_passes (vista : Vista) : closure vista = closurePasses vista vista.nodes.size := by
  have fold (n : Nat) : (List.range n).foldl (fun seen _ => closurePass vista seen)
      ((Array.replicate vista.nodes.size false).set! vista.bottom true) = closurePasses vista n := by
    induction n with
    | zero => rfl
    | succ n ih =>
        simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ih, closurePasses]
  rw [closure_eq_fold]
  exact fold vista.nodes.size

/-- Strictly decreasing references bound the number of backward closure passes. -/
theorem DagReach.marked {vista : Vista} (topological : Topological vista)
    (bottomInside : vista.bottom < vista.nodes.size) {i : Nat}
    (reach : DagReach vista vista.bottom i) :
    i < vista.nodes.size ∧
      (closurePasses vista (vista.nodes.size - 1 - i))[i]?.getD false = true := by
  induction reach with
  | root =>
      refine ⟨bottomInside, closurePasses_mono vista 0 _ (Nat.zero_le _) _ ?_⟩
      simp [closurePasses, bottomInside]
  | @parent i p _ inside parent ih =>
      have less := (topological i inside).1 p parent
      have targetInside := less.trans inside
      refine ⟨targetInside, closurePasses_mono vista (vista.nodes.size - 1 - i + 1) _
        (by omega) p ?_⟩
      exact closurePasses_step vista _ i p inside targetInside ih.2 (Or.inl parent)
  | @incoming i edge _ inside incoming ih =>
      have less := (topological i inside).2 edge incoming
      have targetInside := less.trans inside
      refine ⟨targetInside, closurePasses_mono vista (vista.nodes.size - 1 - i + 1) _
        (by omega) edge.1 ?_⟩
      exact closurePasses_step vista _ i edge.1 inside targetInside ih.2 (Or.inr ⟨edge, incoming, rfl⟩)

theorem closure_complete (vista : Vista) (topological : Topological vista)
    (bottomInside : vista.bottom < vista.nodes.size) (reachable : AllReachable vista) :
    (closure vista).all id = true := by
  rw [Array.all_eq_true]
  intro i hi
  have inside : i < vista.nodes.size := by simpa only [closure_size] using hi
  have marked := (reachable i inside).marked topological bottomInside
  have final := closurePasses_mono vista (vista.nodes.size - 1 - i) vista.nodes.size
    (by omega) i marked.2
  rw [← closure_eq_passes] at final
  simpa only [Array.getElem?_eq_getElem hi, Option.getD_some, id_eq] using final

end Counting.Executable
