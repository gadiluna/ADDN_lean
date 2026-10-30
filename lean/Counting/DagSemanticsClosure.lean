import Counting.DagSemanticsInjective

namespace Counting.Executable

def markIncoming (seen : Array Bool) (incoming : List (Nat × Nat)) : Array Bool :=
  incoming.foldl (fun (flags : Array Bool) (edge : Nat × Nat) => flags.set! edge.1 true) seen

def closeNode (vista : Vista) (seen : Array Bool) (i : Nat) : Array Bool :=
  if seen[i]?.getD false then
    let node := vista.node i
    let withParent := match node.parent with
      | none => seen
      | some p => seen.set! p true
    markIncoming withParent node.incoming
  else seen

def closureFold (vista : Vista) : Array Bool :=
  (List.range vista.nodes.size).foldl (fun flags _ =>
    (List.range vista.nodes.size).foldl (closeNode vista) flags)
    ((Array.replicate vista.nodes.size false).set! vista.bottom true)

/- The generated sparse `if let` matcher is named explicitly so the proof
rewrites the executable branch itself. Only the auxiliary-name style linter
is disabled here; the equation is still checked by the Lean kernel. -/
set_option linter.auxLemma false in
theorem closure_eq_fold (vista : Vista) : closure vista = closureFold vista := by
  have step (i : Nat) (seen : Array Bool) :
      (if seen[i]?.getD false = true then
        closure.match_1 (fun _ => Id (ForInStep (Array Bool))) (vista.node i).parent
          (fun p => pure (ForInStep.yield
            ((vista.node i).incoming.foldl (fun (flags : Array Bool) (edge : Nat × Nat) =>
              flags.set! edge.1 true) (seen.set! p true))))
          (fun _ => pure (ForInStep.yield
            ((vista.node i).incoming.foldl (fun (flags : Array Bool) (edge : Nat × Nat) =>
              flags.set! edge.1 true) seen)))
      else pure (ForInStep.yield seen)) = pure (ForInStep.yield (closeNode vista seen i)) := by
    unfold closeNode markIncoming
    dsimp only
    split
    · cases (vista.node i).parent <;> rfl
    · rfl
  have body := funext (fun i => funext (step i))
  simp only [closure, List.forIn_pure_yield_eq_foldl, pure_bind]
  rw [body]
  simp only [List.forIn_pure_yield_eq_foldl, pure_bind]
  rfl

def Marked (property : Nat → Prop) (seen : Array Bool) : Prop :=
  ∀ i, seen[i]?.getD false = true → property i

theorem marked_set (property : Nat → Prop) (seen : Array Bool) (index : Nat)
    (old : Marked property seen) (current : property index) :
    Marked property (seen.set! index true) := by
  intro i hi
  by_cases eq : index = i
  · exact eq ▸ current
  · simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds, if_neg eq] at hi
    exact old i hi

theorem markIncoming_preserves (property : Nat → Prop) (seen : Array Bool)
    (incoming : List (Nat × Nat)) (old : Marked property seen)
    (keys : ∀ edge ∈ incoming, property edge.1) : Marked property (markIncoming seen incoming) := by
  induction incoming generalizing seen with
  | nil => exact old
  | cons edge rest ih =>
      exact ih _ (marked_set property seen edge.1 old (keys edge (by simp)))
        (fun e he => keys e (by simp [he]))

theorem closeNode_preserves (property : Nat → Prop) (vista : Vista) (seen : Array Bool)
    (old : Marked property seen) (i : Nat)
    (parent : property i → ∀ p, (vista.node i).parent = some p → property p)
    (incoming : property i → ∀ edge ∈ (vista.node i).incoming, property edge.1) :
    Marked property (closeNode vista seen i) := by
  unfold closeNode
  split
  · rename_i hi
    have current := old i hi
    apply markIncoming_preserves property _ _ _ (incoming current)
    cases hp : (vista.node i).parent with
    | none => exact old
    | some p => exact marked_set property seen p old (parent current p hp)
  · exact old

theorem closure_marked (property : Nat → Prop) (vista : Vista)
    (bottom : property vista.bottom)
    (parent : ∀ i, i < vista.nodes.size → property i →
      ∀ p, (vista.node i).parent = some p → property p)
    (incoming : ∀ i, i < vista.nodes.size → property i →
      ∀ edge ∈ (vista.node i).incoming, property edge.1) :
    Marked property (closure vista) := by
  have onePass (order : List Nat) (inside : ∀ i ∈ order, i < vista.nodes.size)
      (seen : Array Bool) (marked : Marked property seen) :
      Marked property (order.foldl (closeNode vista) seen) := by
    induction order generalizing seen with
    | nil => exact marked
    | cons i rest ih =>
        exact ih (fun j hj => inside j (by simp [hj])) _
          (closeNode_preserves property vista seen marked i
            (parent i (inside i (by simp))) (incoming i (inside i (by simp))))
  have passes (order : List Nat) (seen : Array Bool) (marked : Marked property seen) :
      Marked property (order.foldl (fun flags _ =>
        (List.range vista.nodes.size).foldl (closeNode vista) flags) seen) := by
    induction order generalizing seen with
    | nil => exact marked
    | cons i rest ih =>
        exact ih _ (onePass _ (fun _ h => List.mem_range.mp h) seen marked)
  rw [closure_eq_fold]
  apply passes
  apply marked_set property _ vista.bottom _ bottom
  intro i hi
  simp only [Array.getElem?_replicate] at hi
  split at hi <;> simp_all

theorem markIncoming_size (seen : Array Bool) (incoming : List (Nat × Nat)) :
    (markIncoming seen incoming).size = seen.size := by
  induction incoming generalizing seen with
  | nil => rfl
  | cons edge rest ih =>
      exact (ih _).trans (by simp)

theorem closeNode_size (vista : Vista) (seen : Array Bool) (i : Nat) :
    (closeNode vista seen i).size = seen.size := by
  unfold closeNode
  split
  · rw [markIncoming_size]
    split <;> simp
  · rfl

theorem closure_size (vista : Vista) : (closure vista).size = vista.nodes.size := by
  have onePass (order : List Nat) (seen : Array Bool) :
      (order.foldl (closeNode vista) seen).size = seen.size := by
    induction order generalizing seen with
    | nil => rfl
    | cons i rest ih => exact (ih _).trans (closeNode_size vista seen i)
  have passes (order : List Nat) (seen : Array Bool) :
      (order.foldl (fun flags _ =>
        (List.range vista.nodes.size).foldl (closeNode vista) flags) seen).size = seen.size := by
    induction order generalizing seen with
    | nil => rfl
    | cons i rest ih => exact (ih _).trans (onePass _ seen)
  rw [closure_eq_fold]
  exact (passes _ _).trans (by simp)

/-- The actual bounded closure check admits induction from the bottom
through parent and red references. This excludes stored but invisible nodes. -/
theorem valid_nodes_induction (vista : Vista) (valid : vista.valid = true)
    (property : Nat → Prop) (bottom : property vista.bottom)
    (parent : ∀ i, i < vista.nodes.size → property i →
      ∀ p, (vista.node i).parent = some p → property p)
    (incoming : ∀ i, i < vista.nodes.size → property i →
      ∀ edge ∈ (vista.node i).incoming, property edge.1) :
    ∀ i, i < vista.nodes.size → property i := by
  have marked := closure_marked property vista bottom parent incoming
  have allMarked : (closure vista).all id = true := by
    simp only [Vista.valid, Bool.and_eq_true] at valid
    exact valid.2
  intro i hi
  apply marked i
  have hci : i < (closure vista).size := by rw [closure_size]; exact hi
  simp only [Array.all_eq_true] at allMarked
  have h := allMarked i hci
  simpa only [Array.getElem?_eq_getElem hci, Option.getD_some, id_eq] using h

end Counting.Executable
